# The CI interface cache — why a docs-only PR can still pay for the tower

`gate.yml` restores Agda's own `.agdai` interfaces before `make gate` runs, so a
module whose content is unchanged is not re-elaborated. The gap between that
working and not working is the largest single lever in CI — run `make
ci-gate-time` to see the current spread, and `typecheck-performance-numbers.md`
under *The gate in CI* for why that number is fetched and not written down. Same
command, same tree, same checks; the only variable is whether the restored
snapshot is one Agda still considers valid.

**The reason it fails is never the key SHAPE**, which is what everyone guesses
first, this doc's author included. It is *which snapshot the prefix restore-key
can see* — and the answer depends on what has merged recently, not on anything
in the workflow file.

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
`refuted`, `probed` and the two runners' builds also run — it does NOT explain a slow
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

## The second cache: MAlonzo objects, and why its key is the TOOLCHAIN

`make gate` compiles the CLI and the bug-cache runner, each a real GHC compile — the Agda backend
emits MAlonzo Haskell for the whole transitive cone, stdlib included, and then
links a binary. That directory was cached by nothing, so every run paid for all
of it; the figure is in `typecheck-performance-numbers.md` under *The other
uncached third*, and it is a large fraction of a WARM gate rather than a rounding
error on a cold one.

**What makes it worth restoring is that the Agda backend is incremental.** On a
warm `_cli` Agda rewrites the `.hs` of the modules whose interfaces moved, and
GHC's own recompilation check then skips every module whose source did not
change — it reports `[Source file changed]` on exactly the ones that did. The
modules it skips are overwhelmingly the stdlib's, which is also where the bytes
are.

That is why the key names `scripts/install-agda.sh` and not the commit. The
reusable part of this tree is the stdlib's objects, which move only when Agda or
the stdlib does; this repo's own modules are rebuilt on every run whatever the
cache holds, because Agda rewrites their `.hs`. A commit-keyed entry would
therefore upload tens of megabytes per green run to store objects that are
either byte-identical to the last run's or about to be thrown away — straight
into the ceiling above, competing with interface snapshots that are worth more
per byte. A fixed key hits, and `actions/cache` does not re-save on a hit.

**The linked binaries are excluded on purpose.** They are larger than the object
tree they are linked from and they relink on every run regardless, so caching
them is upload with no restore value. The cached path is the object tree alone.

Safety is the same argument as the interface cache one section up: GHC
re-verifies every module's recompilation condition against the `.hs` Agda has
just written, so a stale or absent entry costs a rebuild and can never turn a
check that should fail into one that passes.

## The third cache: the oracle's binaries, and why its key is the CONE

The oracle job shares nothing with the gate. It builds its own two runners from
its own tree (`make cli-build`, whose first half is `make oracle-tree`: the
runners' import cone, copied out of the stripped mirror with termination
checking off and every `{-@0-}` marker made a real `@0` under `--erasure`), and
caches the **linked
binaries** rather than anything they were built from. That is the opposite of
the MAlonzo rule above, for the opposite reason: there the binaries relink on
every run anyway, while here a hit skips Agda altogether — the job does not
even install it.

**The key is `make oracle-key`: a hash of the cone's STRIPPED sources**, plus
`scripts/oracle-mirror.py` and `scripts/install-agda.sh`. So an edit outside
the cone (the whole proof) or a comment edit leaves the binaries standing — a
marker is the one comment the stripper keeps, since it changes the build — and
any edit that could change what the evaluator computes rebuilds them. There
are **no restore-keys**: a near match is a binary of some other evaluator, and
running it would report that evaluator's verdicts as this commit's. A miss is a
cold build of the cone, stdlib included.
