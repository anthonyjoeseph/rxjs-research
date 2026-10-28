# `make old-denotation` — Tier 0's remaining work

Tier 0 moves the proofs from the stream denotation to the table
(`denotation/Table`). It is done when nothing outside the old denotation
reaches it, so the old denotation can be deleted outright. `make
old-denotation` lists every remaining use, by file, and exits 1 while any is
left. **It joins the gate when it reads clean**; until then the count is a
measure, not a failure.

**What counts as the old denotation** (`OLD_DENOTATION` in the Makefile):

- every name of a module that is the denotation and nothing else
  (`--module`), so any import of one is a use;
- in a host module (`--host`), the operator library: every name ending in
  `ᴰ`, and the names given by `--name`. The rest of a host is the engine's
  vocabulary (the runs it shows, their agreement) and stays.

**What counts as a use:** an import of an old module; a host import whose
`using` names an old name; a host imported with no `using`, which takes the
old names wholesale; a qualified `X.name` through a host imported `as X`. The
old modules and the hosts are not scanned: they are the old denotation.

Textual, like the other checkers: it reads import lines, not scope, so a
name brought in by an `open` of a record or a module application is not
seen.

`make old-denotation-selftest` (in the gate) runs it over
`scripts/old-denotation-selftest/`: each way of reaching the old denotation
must fire, and a host's engine vocabulary must not.
