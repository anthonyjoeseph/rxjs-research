# `make bg` — detaching a build that outlives a tool call

```
make bg T=gate-heavy            ← launch, under the Bash tool's run_in_background
make bg-check T=gate-heavy      ← LOOK ONCE: GREEN / RED + failing tail / STILL RUNNING
make bg-wait T=gate       ← WAIT: blocks until terminal, then GREEN or RED + tail
```

**Never hand-roll the wrapper.** The obvious `(cmd > log; echo EXIT=$?)` exits with
`echo`'s status and so reports **every build green**. That is what this replaces.

## `make bg` always exits 7, green or red, by design

Not a propagated status — a deliberately USELESS one. A launcher status that is
right most of the time is worse than one that is never right: the reliable one gets
read and believed, and every rare false green slips through. An invariant 7 carries
no information at all, so it cannot carry a wrong answer, and the only way to learn
anything is `bg-check`, which reads the log. **Never make this "smarter" by
propagating the code; that is the bug, restored.** So **a completion notification is
never a result — `bg-check` is.**

The bug it exists to close is the obvious hand-rolled wrapper:

```
(make gate-heavy > /tmp/x.log 2>&1; echo EXIT=$? >> /tmp/x.log)
```

The subshell exits with ECHO's status, which is ALWAYS 0. So the launcher reports
success no matter what happened, and a RED build is indistinguishable from a green
one unless someone remembers to read the log — which is exactly the thing that did
not happen. Same family as the `timeout … | tail` trap and the `make gate-heavy` run from
the wrong directory: a green-looking lie.

## The signal trap is load-bearing

Its absence produced the one failure this whole apparatus is supposed to be immune
to. `EXIT=` is written AFTER the sub-make returns, so a build killed by a signal —
the whole process group going down, e.g. because the launcher was run inside a
foreground command that hit a tool timeout — left the log with NO terminal marker.
`bg-check` then reported STILL RUNNING for a build that was already dead, and
`bg-wait` would have blocked forever waiting for a line nobody was going to write.
**A hang is not a safer failure than a false green; it is the same defect pointed
the other way, and it is worse for being patient.**

So the recipe traps TERM/INT/HUP and writes a terminal `EXIT=143` plus a line saying
the build was KILLED rather than failed — the distinction matters, because a bare 143
sends the reader hunting for an Agda error that does not exist. Two constraints, both
learned by breaking them:

- **The explanation goes on its OWN line, above the marker.** `bg-check` parses
  `EXIT=` and does `exit $ec`, so any prose on that line becomes extra arguments and
  the shell errors out mid-verdict.
- **`EXIT=143` alone, never the real signal number.** `bg-check` only needs "terminal
  and nonzero", and inventing per-signal codes gives the reader a distinction that
  carries nothing.

**AND THE LESSON THAT PROMPTED IT: launch `make bg` under the Bash tool's OWN
background flag, never inside a foreground compound command.** `make bg` detaching
the build does NOT protect it — the timeout kills the group.

`bg-check` exits 3 while running and 1 when red, so the two are distinguishable at
the script level — but not through `make`, which collapses both to its own exit 2.
Hence the rule above. `LOG=<path>` overrides the log location; `I=<n>` sets
`bg-wait`'s poll interval in seconds.

## Do not loop on `bg-check`

Make collapses every recipe failure to its own exit 2, so still-running and failed
become the same number and the distinction dies at make's boundary. A loop keyed on
the specific code either exits on the first poll and calls a running build finished
(observed: a gate with 62 log lines and half the tower still to check) or spins
forever on a dead RED one. Both are the false green `make bg`'s invariant exit
exists to prevent, arriving one level up.

**`bg-check` to LOOK once, `bg-wait` to WAIT.** `bg-wait` blocks until the log is
TERMINAL, so its nonzero can only mean RED — the one thing `bg-check` cannot offer
at any exit code.

## Counting the builds — `ps aux | grep "[b]in/agda"`

The concurrency rule the campaign runs under ("while a gate is live, run no other
check") is only enforceable if you can SEE the live one, and the obvious pattern
does not: Agda's command line is `.../bin/agda -W error src/Main.agda`, with no
`--` in it, so a grep for `agda --` counts zero however many builds are running.
A zero that means "my pattern is wrong" and a zero that means "the machine is
quiet" are indistinguishable, and the wrong one licenses a second launch.

Measured cost of getting this wrong once: three builds racing on one interface
cache, each dying at a later module than the last with no error text, read three
times as a build being KILLED. It is what a race looks like from outside, and
the reading sends you at the module the log happens to name.

```
ps aux | grep "[b]in/agda" | wc -l     0 means quiet, and means it
pkill -9 -f "libexec/ghc"              what actually reaps a wedged one
```

The second line is there because `pkill -f "bin/agda"` misses: the binary lives
under a `libexec/ghc-*-inplace` path, and one process survived two rounds of the
narrower pattern.

## macOS

`setsid` and `timeout` DO NOT EXIST. Piped to `tail`, the `$?` you read is `tail`'s
zero. Detach with the Bash tool's `run_in_background`.

## No keep-alives

The session runs on a persistent laptop, so the container does not suspend between
tool calls — background workers and detached builds advance on their own, and worker
completion notifications wake the design session. Keep only a SPARSE fallback
check-in (~60 min) to catch workers wedged by harness restarts: a restart kills a
worker's in-flight turn, diagnosed via transcript mtime + `ps` and revived via
SendMessage with re-verify instructions. **"queued" = alive, "resumed from
transcript" = was dead.**
