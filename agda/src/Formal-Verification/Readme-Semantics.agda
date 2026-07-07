-- README SEMANTICS PROOFS — the root README.md's semantics-by-edge-case,
-- each a top-line result checked against the Agda spec.
--
-- Every edge-case section of ../../../README.md is a concrete program run
-- under a concrete driver, with a stated output. Here that output is a
-- machine-checkable claim: `spec-batchSimultaneous em prog ≡ expected`,
-- i.e. the Agda spec REPRODUCES the README's example exactly. This is the
-- formal link between the two spec sources of truth (the README prose and
-- the Agda denotation) — discharge it and any drift between them becomes a
-- typecheck failure.
--
-- STATUS: postulated. Next phase discharges each (each is a closed ground
-- computation, so the intended proof is `refl` once it holds — a failure
-- to reduce to `refl` is exactly a drift to investigate).
--
-- Every postulate below is hyperlinked from its section in README.md.
module Formal-Verification.Readme-Semantics where

open import Prelude
open import Shared-Types
open import Spec.Batch-Simultaneous

------------------------------------------------------------------------
-- source-slot names (read the driver's Fin n indices)

private
  s0 : {n : ℕ} → Fin (suc n)
  s0 = fzero

  s1 : {n : ℕ} → Fin (suc (suc n))
  s1 = fsuc fzero

------------------------------------------------------------------------
-- The flagship diamond (README §"The idea: provenance + batchSimultaneous")
--
--   const tenfold = s.pipe(map((n) => n * 10));
--   merge(s, tenfold).pipe(batchSimultaneous())…
--   s.next(5); // [5, 50]
--   s.next(6); // [6, 60]

diamond : Exp 1
diamond = mergeAllE (ofS (srcE s0 ∷ mapE (λ n → n * 10) (srcE s0) ∷ []))

diamond-driver : Emissions 1
diamond-driver = emissions (pureV []) ((s0 , 5) ∷ (s0 , 6) ∷ [])

postulate
  readme-diamond :
    spec-batchSimultaneous diamond-driver diamond
      ≡ (5 ∷ 50 ∷ []) ∷ (6 ∷ 60 ∷ []) ∷ []

------------------------------------------------------------------------
-- One subscribe() call is one batch (README §"One subscribe() call is one batch")
--
--   merge(of(1, 2), of(3))…  // [1, 2, 3] — one instant (the frame).
-- (The `timer(100)` tail is out of grammar — no scheduler primitive; the
--  representable claim is that the whole static frame is a single batch.)

one-subscribe : Exp 0
one-subscribe = mergeE (ofE (1 ∷ 2 ∷ [])) (ofE (3 ∷ []))

one-subscribe-driver : Emissions 0
one-subscribe-driver = emissions (pureV []) []

postulate
  readme-one-subscribe-one-batch :
    spec-batchSimultaneous one-subscribe-driver one-subscribe
      ≡ (1 ∷ 2 ∷ 3 ∷ []) ∷ []

------------------------------------------------------------------------
-- Each .next() call is its own instant (README §"Each .next() call is its own instant")
--
--   const doubled = a.pipe(map((n) => n * 2));
--   merge(a, doubled, b)…
--   a.next(5); // [5, 10]
--   b.next(7); // [7]
--   a.next(6); // [6, 12]

each-next : Exp 2
each-next = mergeAllE (ofS (srcE s0 ∷ mapE (λ n → n * 2) (srcE s0) ∷ srcE s1 ∷ []))

each-next-driver : Emissions 2
each-next-driver = emissions (pureV []) ((s0 , 5) ∷ (s1 , 7) ∷ (s0 , 6) ∷ [])

postulate
  readme-each-next-own-instant :
    spec-batchSimultaneous each-next-driver each-next
      ≡ (5 ∷ 10 ∷ []) ∷ (7 ∷ []) ∷ (6 ∷ 12 ∷ []) ∷ []

------------------------------------------------------------------------
-- Cascades inherit their trigger's instant (README §"Cascades inherit their trigger's instant")
--
--   const spawned = s.pipe(mergeMap((n) => of(n * 10, n * 10 + 1)));
--   merge(s, spawned)…
--   s.next(5); // [5, 50, 51]

cascades : Exp 1
cascades =
  mergeAllE (ofS ( srcE s0
                 ∷ mergeMapE (λ n → ofE (n * 10 ∷ ((n * 10) + 1) ∷ [])) (srcE s0)
                 ∷ []))

cascades-driver : Emissions 1
cascades-driver = emissions (pureV []) ((s0 , 5) ∷ [])

postulate
  readme-cascades-inherit :
    spec-batchSimultaneous cascades-driver cascades
      ≡ (5 ∷ 50 ∷ 51 ∷ []) ∷ []

------------------------------------------------------------------------
-- Completion cascades inherit too (README §"Completion cascades inherit too")
--
--   const firstOnly = s.pipe(take(1));
--   const thenSeven = concat(firstOnly, of(7));
--   merge(s, thenSeven)…
--   s.next(5); // [5, 5, 7]
--   s.next(6); // [6]

completion-cascades : Exp 1
completion-cascades =
  mergeAllE (ofS ( srcE s0
                 ∷ concatE (takeE 1 (srcE s0)) (ofE (7 ∷ []))
                 ∷ []))

completion-cascades-driver : Emissions 1
completion-cascades-driver = emissions (pureV []) ((s0 , 5) ∷ (s0 , 6) ∷ [])

postulate
  readme-completion-cascades :
    spec-batchSimultaneous completion-cascades-driver completion-cascades
      ≡ (5 ∷ 5 ∷ 7 ∷ []) ∷ (6 ∷ []) ∷ []

------------------------------------------------------------------------
-- share: connect at first subscription, no replay (README §"share: connect at first subscription, no replay")
--
--   const shared = of(5).pipe(share());
--   merge(shared, shared)…  // [5] — once, not twice
--
-- letShare binds the shared source at de-Bruijn 0; the pre-order-first ref
-- is the connecting one (shareE true 0), the second a late ref (shareE false 0).

share-no-replay : Exp 0
share-no-replay =
  letShareE (ofE (5 ∷ []))
            (mergeAllE (ofS (shareE true 0 ∷ shareE false 0 ∷ [])))

share-no-replay-driver : Emissions 0
share-no-replay-driver = emissions (pureV []) []

postulate
  readme-share-connect-no-replay :
    spec-batchSimultaneous share-no-replay-driver share-no-replay
      ≡ (5 ∷ []) ∷ []

------------------------------------------------------------------------
-- Late subscribers see only later events — diamonds grow (README §"Late subscribers see only later events — diamonds grow")
--
--   const shared = src.pipe(share());
--   const growing = trigger.pipe(mergeMap(() => shared));
--   merge(shared, growing)…
--   trigger.next(); src.next(7); // [7, 7]
--   trigger.next(); src.next(8); // [8, 8, 8]
--
-- slot 0 = src, slot 1 = trigger; each trigger firing adds one live ref of
-- the hot share (which never replays, so a trigger instant alone is empty).

late-join : Exp 2
late-join =
  letShareE (srcE s0)
            (mergeAllE (ofS ( shareE true 0
                            ∷ mergeMapE (λ _ → shareE false 0) (srcE s1)
                            ∷ [])))

late-join-driver : Emissions 2
late-join-driver =
  emissions (pureV []) ((s1 , 0) ∷ (s0 , 7) ∷ (s1 , 0) ∷ (s0 , 8) ∷ [])

postulate
  readme-late-join-growth :
    spec-batchSimultaneous late-join-driver late-join
      ≡ (7 ∷ 7 ∷ []) ∷ (8 ∷ 8 ∷ 8 ∷ []) ∷ []

------------------------------------------------------------------------
-- take counts values, even mid-batch (README §"take counts values, even mid-batch")
--
--   const doubled = s.pipe(map((n) => n * 2));
--   const firstThree = merge(s, doubled).pipe(take(3));
--   firstThree…
--   s.next(5); // [5, 10]
--   s.next(6); // [6] — take(3) cuts the second batch in half

take-counts : Exp 1
take-counts =
  takeE 3 (mergeAllE (ofS (srcE s0 ∷ mapE (λ n → n * 2) (srcE s0) ∷ [])))

take-counts-driver : Emissions 1
take-counts-driver = emissions (pureV []) ((s0 , 5) ∷ (s0 , 6) ∷ [])

postulate
  readme-take-counts-values :
    spec-batchSimultaneous take-counts-driver take-counts
      ≡ (5 ∷ 10 ∷ []) ∷ (6 ∷ []) ∷ []

------------------------------------------------------------------------
-- Batch order is delivery order (README §"Batch order is delivery order")
--
--   const shared = src.pipe(share());
--   const doubled = shared.pipe(map((n) => n * 2));
--   const sums = merge(shared, doubled).pipe(scan((acc, n) => acc + n, 0));
--   sums…
--   src.next(5); // [5, 15]
--   src.next(1); // [16, 18]

batch-order : Exp 1
batch-order =
  letShareE (srcE s0)
            (scanE (λ acc n → acc + n) 0
                   (mergeAllE (ofS ( shareE true 0
                                   ∷ mapE (λ n → n * 2) (shareE false 0)
                                   ∷ []))))

batch-order-driver : Emissions 1
batch-order-driver = emissions (pureV []) ((s0 , 5) ∷ (s0 , 1) ∷ [])

postulate
  readme-batch-order-is-delivery-order :
    spec-batchSimultaneous batch-order-driver batch-order
      ≡ (5 ∷ 15 ∷ []) ∷ (16 ∷ 18 ∷ []) ∷ []

------------------------------------------------------------------------
-- The serial joins mirror rxjs (README §"The serial joins mirror rxjs")
--
--   const burst = of(1, 2);
--   const exhausted = burst.pipe(exhaustMap((n) => of(n * 10)));
--   exhausted…  // [10, 20] — both sync inners run, one frame
--
-- exhaustMap f e = exhaustAll (map (λ v → f v) e); a synchronous inner
-- closes before the next arrival, so neither is dropped.

serial-joins : Exp 0
serial-joins = exhaustAllE (mapS (λ n → ofE (n * 10 ∷ [])) (ofE (1 ∷ 2 ∷ [])))

serial-joins-driver : Emissions 0
serial-joins-driver = emissions (pureV []) []

postulate
  readme-serial-joins-mirror-rxjs :
    spec-batchSimultaneous serial-joins-driver serial-joins
      ≡ (10 ∷ 20 ∷ []) ∷ []
