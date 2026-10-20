# `make roadmap-check` — the gate on PROOF-STATE.md (and CLAUDE.md's dates)

`scripts/check-roadmap.py --prune`. The rules PROOF-STATE lives by are CLAUDE.md's
("PROOF-STATE.md — the risk ledger"); this is the half a machine can see.

## The file's shape

```
## Tier N — <name>
<preamble: what the tier exports>
### Progress
<what is established toward settling the top group>
### Ledger
#### <GROUP NAME>
<the shared design issue; what would settle it>
Members: `name`, `name-{a,b}`, `family-*`.
```

Groups are ranked riskiest first. The order is a judgement, so it is not checked.

## Checks

1. **Coverage** — every live postulate (`scripts/check-wiring.py --postulates`) is a
   member of some group. No postulate can be added and not filed.
2. **One group** — no live postulate is a member of two groups. A group is one design
   issue; a postulate in two has its risk counted twice.
3. **Staleness, pruned** — a member naming nothing live is REMOVED from its `Members:`
   line, and a group left with no members is DELETED, heading and all. Deleting or
   discharging a postulate costs nothing (Anthony). The check reports what it pruned.
4. **Shape** — every group has a `Members:` line and sits under a `### Ledger`; a tier
   with groups has a `### Progress`.
5. **Budgets** — prose characters, backticked names free: the file's preamble
   (`FILE_BUDGET`), a tier's preamble (`TIER_BUDGET`), a tier's progress
   (`PROGRESS_BUDGET`), a group's block (`GROUP_BUDGET`). Research that outgrows its
   budget belongs in a source header.
6. **No dates** — in PROOF-STATE.md, CLAUDE.md and `docs/*.md`. PROOF-STATE must be
   current and the rules timeless; a date is history arriving with its timestamp.

Member shorthand: `{a,b}` brace expansion (live if ANY alternative is live) and `*`
globs. Names only — a collective phrase in prose names nothing the check can see.

## `make roadmap-selftest`

Fixtures in `scripts/roadmap-selftest/`, against fixture ledgers rather than the real
one. `good.md` must pass; each failing fixture must fail AND name its check; the prune
path runs on a copy and must leave a green file with the dead member, and the emptied
group, gone — and the live group kept.
