# `make port-check` — the port boundary

Tier 0 carries the old adequacy proof (`adequacy/`, `operation/Machine.agda`) to
the state tree, in `agda-impl/port/`. The boundary is that the port **only
ports**: work the old proof left undone is Tier 1's, never the port's.

`scripts/check-port.py` reads the old tower at `PORT_BASE` (the Makefile) out of
git, and checks every non-private top-level declaration under `port/`:

| Finding | Meaning |
| --- | --- |
| `NEW NAME` | the old tower declares no such name |
| `FILLED GAP` | every old declaration of the name is a postulate, the port's is not |
| `NO OLD BODY` | the port postulates a name that had a body, and does not say where |
| `BAD OLD BODY` | an `OLD BODY` line whose commit, path or name does not resolve to a body |

A postulated old body carries, in the comment block directly above it:

```
-- OLD BODY: <sha> <path from the repo root>
```

**Matching is by name only.** A ported declaration's type changes with the
engine under it; its name does not. Same name, same role.

**Free:** a `private` declaration, anything in a `where`, a data type's
constructors and a record's fields. They belong to the body they serve.

**`PORT_BASE` moves only by hand.** The old tower is what the port answers to,
so it stays frozen while the port runs. The gate job checks out full history, so
the commit always resolves.

`make port-selftest` runs the checker over `scripts/port-selftest/` against the
real old tower: each way out of the boundary must fire, and each way to stay
inside must not.
