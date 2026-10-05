# Handoff

## Where the work is

We are working tier 2, on the first roadmap leg in PROOF-STATE.md: "Split the cascade per path constructor". The tier's monster is `simulation`. Read CLAUDE.md first, then PROOF-STATE.md. The legs in PROOF-STATE are the schedule.

## What this commit lands

This commit proves `finish-store`. It was a postulate classed FALSITY, NO EVIDENCE; it is now a real definition in the new module `agda/src/Simulation/Finish.agda`, wired in through `Simulation.Statement`. It shows that a cascade's last-arrival drop keeps the two stores related:

- The drop removes the same rows from both registries (`drop-rows`).
- The sweep guards stay pointwise equal after the drop (`pw-agree`).
- The live sweep preserves the pointwise relation, uniqueness, boundedness and Sync. This is `sweepL-pw` and its siblings.
- The kept source pairs are re-indexed through the sweep (`regrel-sweep`).

The proof needed two new invariants, and they went into the records rather than into signatures:

- **`Store.swept`:** each live slot's sweep guard agrees on both sides. The guard itself is `guardOf`, defined in `Simulation.Stores`.
- **`Arr.lists`:** the arrival's source pair is or is not listed on both sides at the same time (`SameAt`).

The old `wfᴾ`/`wfᴵ` fields were removed because they are unsound. An exact merge-lane-count field is false between the end walk and the drop. This is recorded as a `DEAD ROUTE` in the header of `record Store`.

**What the new fields cost:** every postulated cascade arm now also owes persistence of `swept` and `lists`. The affected arms are outer, inner, lane, take, takeWhile, hot, deferInner, block, hop and scan. That debt is the price of the invariants being true, and it is the next work.

## Verification status

- **Dev checks:** `make agda-dev` is green on `Finish`, `Statement`, `Stores`, `Pass`, `Pop`, `Walk`, `Chains` and `Close`.
- **Local gate:** `make gate-cheap` is green.
- **Not re-checked:** `agda/evidence/probed/Probed/Stores.agda` (two lines removed for `wfᴾ`/`wfᴵ`).
- **CI on this commit:** may go red, and that is acceptable for this handoff. The heavy tower (`gate-heavy`) has not been run on this commit. Per CLAUDE.md it is never run locally; CI runs it.
- **CI on the previous commit:** the `gate` check was already red on `d27dc781`, with `make gate` exiting 2. The other three jobs (quickcheck, ts, oracle) were green. The built-in `gh` cannot fetch the job log, and I did not diagnose the failure.
  - **Likely cause:** an earlier version of the `comments-check` stranded-prose issue that I fixed locally in this commit (unindented `DEAD ROUTE` continuation lines).
  - **To confirm:** open the job log in the GitHub UI.
  - **If the gate is still red:** it is most likely the tower (termination or a warning in a module this commit touches), or `refuted`/`probed`.

## Next steps

1. Watch PR #279 CI on this commit. Fix whatever `make gate` reports.
2. Continue the first leg. Make each remaining arm a real body, one leaf per path constructor, with each arm carrying `swept` and `lists` forward.
   - Work topmost and riskiest first: `hot-end-start`, `hot-finish`, `hot-start`, `hot-adm`, `read-arm`, then the outer/inner/lane arms.
   - Write `lane-arm` as a definition over `inner-arm`.
3. After that, the other rows in the leg: `sink-pass`, `root-values`, `init-{numbers,distinct}`, `cascade-stamps`, `subscribe-stamps` and the `Walk` leaves.

## Agda traps from this leg

- **Explicit implicits:** `dropSource s ?rs` is not solved by unification. Pass `{rs = …} {rs′ = …}` explicitly.
- **As-patterns:** rebuilding a constructor with `refl` is circular. Use an as-pattern instead (`rr@(read~ …)`).
- **Holes mask errors:** a `{!!}` hole hides unsolved-meta errors, so bisecting with holes misleads.
