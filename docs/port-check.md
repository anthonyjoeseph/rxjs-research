# `make port-check` — the port boundary

Tier 0 carries the adequacy and simultaneous proofs (`adequacy/`,
`simultaneous/`) from the stream denotation to the emission set, in place. The
boundary is that the port **only ports**: work the old proof left undone is
Tier 1's, never the port's.

**Delete this tool when Tier 0 is discharged** (Anthony): the script, its selftest,
its Makefile and gate entries, this doc and the `OLD BODY` markers.

`scripts/check-port.py` reads the old tower (`PORT_SCOPE` at `PORT_BASE`, both in
the Makefile) out of git, and checks every non-private top-level declaration
in the scope. **Bodies and postulates answer to different rules:** a body must
be an old one, carried over; a postulate only states a gap, so a new one is
free.

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

**The scope is `PORT_SCOPE` and its import cone.** The scope is the old tower
itself, ported in place, so every declaration in it is checked, those it
already had included: an old postulate filled where it stands is a
`FILLED GAP`. In a cone module outside the scope, only declarations it has
gained since `PORT_BASE` are checked, so a body cannot leave the boundary by
moving into a module the port imports (`denotation/` included); a new fact
there is a postulate.

**Matching is by name only.** A ported declaration's type changes with the
denotation under it; its name does not. Same name, same role. **`xᵀ` is `x`'s
emission set reading** and answers to the old `x` as well as to its own name.

**Free:** a `private` declaration, anything in a `where`, a data type's
constructors and a record's fields. They belong to the body they serve.

**`PORT_BASE` moves only by hand.** The old tower is what the port answers to,
so it stays frozen while the port runs. The gate job checks out full history, so
the commit always resolves.

`make port-selftest` runs the checker over `scripts/port-selftest/` against a
tower frozen with the fixtures (`PORT_SELFTEST_BASE`): each way out of the
boundary must fire, in a port directory and in place, and each way to stay
inside must not.
