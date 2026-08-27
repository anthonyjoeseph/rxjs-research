# `scripts/stub-proofs.py` — a `src` mirror with the PROOFS postulated

## What it does

Reads the comment-stripped `src` mirror and writes a copy in which every
declaration whose **result type** — the text after its last top-level `→` —
mentions `≡`, `≤`, `<` or `⊥` has its body replaced by a `postulate` at the
same signature.  Measured on the tree: **1338 proofs across 91 files.**

```
python3 scripts/stub-proofs.py --src agda/_stripped-comments/src --dest <out>
python3 scripts/stub-proofs.py --selftest
```

## Why the rule is about the RESULT type

The evidence trees need definitions to REDUCE — a probe is `refl` at concrete
inputs and a postulate does not compute — but they never unfold a proof term.
So `capsOK? : … → Bool`, `Stream : … → Set` and `nestB : … → ℕ` keep their
bodies while `k≤3^k` and `∧-true` do not.  A proposition appearing only in an
ARGUMENT does not make a declaration a proof; that case is in the selftest,
because getting it wrong would stub the decision procedures.

It reuses `agda-dev.py`'s declaration parser rather than adding a second parser
for the same language.

## What it leaves alone, and what that costs

`private`, `abstract`, `mutual`, `instance`, `data` and `record` blocks pass
through untouched.  An `abstract` body is already opaque to the checker, so
there was nothing to buy there anyway.

## Line numbers are preserved exactly

A stub is `postulate` plus the signature indented by two — one line more than
the signature — and the extra line is taken back from the clause block it
replaces.  Every file comes out line-exact, so `unmap-positions.py` still
resolves positions onto `agda/src`.

## Why it is NOT on the gate path

Measured against the tree it would run on, it saves **14 s** on a normal commit
(`refuted` 17.5 s → 4.4 s; `probed` does not move at all, and cannot — see
`typecheck-performance-numbers.md`).  Against that it wants a fourth
`.agda-lib`, a generation step, and it gives up the property that the evidence
targets incidentally re-check that `src` still typechecks.  The instrument is
kept because it is re-runnable and the measurement is worth repeating when the
tree's shape changes; wiring it in is a decision the numbers do not currently
force.
