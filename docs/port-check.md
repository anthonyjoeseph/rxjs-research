# `make port-check` — the port boundary

Tier 0 carries the old adequacy proof (`adequacy/`, over the old engine's
`operation/{AbstractObservable,PureObservable,Observable}.agda`) to the
pointer-free engine in `agda-impl/port/`, so the preservation half needs no
grid. The boundary is that the port **only
ports**: work the old proof left undone is Tier 1's, never the port's.

**Delete this tool when Tier 0 is discharged** (Anthony): the script, its selftest,
its Makefile and gate entries, this doc and the `OLD BODY` markers.

`scripts/check-port.py` reads the old tower at `PORT_BASE` (the Makefile) out of
git, and checks every non-private top-level declaration under `port/`. **Bodies
and postulates answer to different rules:** a body must be an old one, carried
over; a postulate only states a gap, so a new one is free.

| Finding | Meaning |
| --- | --- |
| `NEW NAME` | a definition, data type or record the old tower has no name for |
| `FILLED GAP` | every old declaration of the name is a postulate, the port's is not |
| `NO OLD BODY` | the port postulates a name the old tower never postulated, and does not say where its body is |
| `BAD OLD BODY` | an `OLD BODY` line whose commit, path or name does not resolve to a body |

A postulated old body carries, in the comment block directly above it:

```
-- OLD BODY: <sha> <path from the repo root>
```

**The scope is `port/` and its import cone**, the old tower aside, so a body
cannot leave the boundary by moving into a module the port imports. In a
module that existed at `PORT_BASE`, under `port/` or in its cone, only
declarations it has gained since are checked: the engine the port runs on
(`port/operation/`) predates the port and is not part of it.

A module renamed since `PORT_BASE` (`PORT_RENAMED` in the Makefile) counts what
it declared under its old path as well.

**Matching is by name only.** A ported declaration's type changes with the
engine under it; its name does not. Same name, same role.

**Free:** a `private` declaration, anything in a `where`, a data type's
constructors and a record's fields. They belong to the body they serve.

**A port module is a whole copy.** It carries the old module's engine-free
declarations too, so the old module is deleted outright when the port replaces
it; `make dup-check` reads a `port/` declaration named as one outside `port/` as
that one carried over. Delete that exemption with this tool.

**`PORT_BASE` moves only by hand.** The old tower is what the port answers to,
so it stays frozen while the port runs. The gate job checks out full history, so
the commit always resolves.

`make port-selftest` runs the checker over `scripts/port-selftest/` against the
real old tower: each way out of the boundary must fire, and each way to stay
inside must not.
