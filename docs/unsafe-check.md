# `make unsafe-check` — policing pragmas by grep

**The build is not `--safe`, and nothing mechanically stops an unsafe pragma.**
`make gate-heavy` runs a plain `agda src/Main.agda`, and a live `{-# TERMINATING #-}`
already sits in the QuickCheck module, off the proof path.

So the policing is textual. `make unsafe-check` covers:

- `TERMINATING`
- `NON_TERMINATING`
- `NO_POSITIVITY_CHECK`
- `NO_UNIVERSE_CHECK`
- `REWRITE`
- `--type-in-type`

**Anything it finds on the proof path is a soundness hole, and no mandate in
CLAUDE.md authorises it.**

`--safe` cannot be enabled today (it rejects `postulate`, and we have dozens by
design), but it IS the finish-line certificate: the day `The-Proof.agda` is
discharged, `agda --safe src/Main.agda` verifies "no postulates AND no unsafe pragma"
in one command. Changing a flag invalidates interfaces — it is not a free query.
