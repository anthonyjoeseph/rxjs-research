# The CI interface cache — why a docs-only PR can still pay for the tower

`gate.yml` restores Agda's own `.agdai` interfaces before `make gate` runs, so a
module whose content is unchanged is not re-elaborated. When that works, a PR
touching no Agda file finishes in minutes. When it does not, the same PR pays a
near-cold tower — and the reason is never the key SHAPE, which is what everyone
guesses first. It is *which snapshot the prefix restore-key can see.*

## What is cached, and why it is two directories

Agda resolves a file's build directory by walking UP to the nearest enclosing
`.agda-lib`. `agda/_stripped-comments/evidence/` has its own, so a `refuted` or
`probed` file's interface lands under `evidence/_build` while everything in
`src` lands in the top-level one. Caching only the top-level directory leaves
the evidence trees cold on every run regardless of the cache — caught live, on a
dispatched run against an unchanged commit that should have been instant and
instead sat re-checking a nest-cascade refutation.

## The restore is not the light-gate bet, and confusing the two costs a diagnosis

`.gate-heavy-stamp` is a Makefile-level shortcut that skips whole check
CATEGORIES; it is gitignored, so CI never has one and `make gate` always takes
the full heavy path. The interface cache is a different thing entirely: every
check still runs, every file is still considered, and Agda re-verifies each
module's validity key itself. So **"CI takes the heavy path" explains why
`refuted`, `probed` and the bug cache also run — it does NOT explain a slow
tower.** A warm heavy gate skips unchanged modules. If the tower is slow, the
cache is stale, and the routing is a red herring.

## THE TRAP: a PR-scoped cache is invisible to everything except that PR

Actions scopes a cache to the branch that wrote it. A run on `refs/pull/N/merge`
can READ `refs/heads/main`'s entries, but everything it WRITES is visible only
to that same PR. Three consequences, and the third is the expensive one:

- A PR's own second push restores its first push's snapshot. This is real and
  worth keeping — it is what makes re-running a long gate on a fixed-up branch
  cheap.
- No PR ever warms another PR, and no PR ever warms main.
- **The push-to-main run is the ONLY producer of a shared snapshot**, and it
  takes as long as any other gate. So there is a window, the whole length of one
  gate run, in which main's newest cached snapshot is the commit BEFORE the merge
  that just landed. A PR opened or re-pushed inside that window restores a
  snapshot that predates every Agda commit the merged PR carried, and rebuilds
  their entire consumer cone — however small its own diff is.

That window is the usual answer to "why is the gate slow on a PR that changes no
Agda files", and nothing about the cache is misconfigured when it happens. The
fix is patience or a re-run, not a key change.

## The 10 GB ceiling is a correctness problem, not tidiness

GitHub enforces a hard per-repo cache ceiling by evicting least-recently-used
entries. Interface snapshots run tens of megabytes each and every green run
writes a fresh one, so the store fills on its own. Once it is full, the entry
being evicted to make room for the newest one can be the newest one's only
useful predecessor — the store punishes the branch that uses it most.

Dead PR scopes are the bulk of it and are pure loss: unreachable by
construction the moment the PR closes, and still counted against the ceiling.
At the sweep that produced `cache-prune.yml` the store held 127 entries at
9.94 GB, of which 74 entries and 5.71 GB belonged to PRs that had already
merged or closed.

`cache-prune.yml` deletes a PR's caches when it closes, sweeps for any the event
missed, and trims main's interface snapshots to the newest few — only the newest
is ever restored, since the restore-key takes the most recent prefix match.
**Do not instead stop saving on PR branches**: that removes a benefit the repo
actually collects, to avoid a cost that a scheduled job removes for free.
