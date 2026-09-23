# Handoff — tier 1, the `stuck-hop` crashes

Temporary. It records what one session found so the next can pick up without
re-deriving it. Delete it, and `temp-handoff-crash-seeds.txt` with it, once its
contents have moved to PROOF-STATE.md, the source headers, or git history. CLAUDE.md is still the law; read it first, then
PROOF-STATE.md's Tier 1 section.

## Where things stand

- **Branch:** `claude/tier-1-progress-review-dxbweg`, PR #277 ("tier 1: give the
  share's connect a consumer"). All work is pushed.
- **`make gate` is green on the heavy path.** That covers the full tower through
  `Main`, both evidence trees, and termination of the rewritten mutual block.
  CI is green on the branch head.
- **The goal of Tier 1** is the differential oracle matching rxjs on every
  program, with both postulates `stuck-hop` and `stuck-finish` discharged. Both
  sit in `agda/src/Rx/Evaluator/Reducible.agda`.

## The 1.5M sweep on the current evaluator

| Outcome | Cases |
| --- | --- |
| Run | 1,500,000 |
| Match rxjs | 1,492,121 |
| Diverge from rxjs | 0 |
| Time out | 0 |
| Crash at `stuck-hop` | 7,879 |
| Crash at `stuck-finish` | 0 |

The 7,879 crash rows hold 7,833 distinct programs; the generator repeats some.
Every one of them has a `batchSync` nested beneath a flattener (`mergeAll`,
`switchAll` or `exhaustAll`). In 171 of them the `batchSync` sits inside a
shared slot's definition rather than the main expression.

That is the shape already pinned as
`typescript/cases/candidate-dropped-under-a-frame.ndjson`. The cause is written
in the `stuck-hop` header in Reducible: a frame that changes the element type
answers with the continuation it was handed, not its parent's successor. A cell
written below such a frame is stale to the next fold, so the fold's runtime
certification fails and vouches `nothing` at `obs`, which is the branch.

Flattener counts across the distinct programs overlap, since a program can hold
more than one flattener:

| Flattener present | Programs |
| --- | --- |
| `mergeAll` | 4,218 |
| `switchAll` | 3,303 |
| `exhaustAll` | 3,213 |

About 37% of the crashers have a shared slot, so the shape does not need a
share.

## How to reproduce the crashes

Build the CLI first, as a background tool call, then check it. `make bg` always
exits non-zero by design, so its completion notice is never the result.

```
make bg T=cli-build        # background tool call; about 40–65 min when Reducible changed
make bg-check T=cli-build  # GREEN / RED / STILL RUNNING
```

The sweep is deterministic: two runs gave identical counts. It takes about
twenty minutes.

```
cd typescript
npm run --silent oracle -- --corpus 1500000 --crashes /path/to/crashes.ndjson > sweep.log 2>&1
tail -1 sweep.log
```

### Faster: rebuild all 7,833 crashers from their seeds

`temp-handoff-crash-seeds.txt`, beside this file, lists every distinct crasher
as `s<seed>:<position>`, one per line. The sweep draws seed `s<i>` through
`genTestCases`, which yields twenty cases per seed from a seeded generator, so a
seed and a position name one program exactly. The list is valid only while
`typescript/src/generator.ts` is unchanged from this branch's head: any edit to
the generator moves every position.

Rebuilding and replaying the whole set was checked: 7,833 cases rebuilt, all
7,833 crash at `stuck-hop`, in about three minutes. This compiles the harness to
a throwaway directory and rebuilds the cases:

```
cd typescript
./node_modules/.bin/tsc --outDir .seedmap-tmp --rootDir src --noEmit false
cat > .seedmap-tmp/regen.mjs <<'EOF'
import { readFileSync, writeFileSync } from "node:fs";
import { genTestCases } from "./generator.js";
import { serialize } from "./serialize.js";
const [seedFile, outFile] = process.argv.slice(2);
const rows = readFileSync(seedFile, "utf8").split("\n")
  .filter((l) => /^s\d+:\d+$/.test(l))
  .map((l) => { const [seed, j] = l.split(":"); return serialize(genTestCases(seed)[Number(j)]); });
writeFileSync(outFile, rows.join("\n") + "\n");
console.log(`${rows.length} cases written to ${outFile}`);
EOF
node .seedmap-tmp/regen.mjs ../temp-handoff-crash-seeds.txt crash-cases.ndjson
rm -rf .seedmap-tmp
npm run --silent oracle -- --cases crash-cases.ndjson
```

A single seed also replays directly, with every case it yields rather than just
the crasher: `npm run oracle -- --seed s44` runs the seed holding the first
listed crasher.

### From scratch: the sweep's own crash file

Rows written by the crashes flag are wrapped as an object with a `why` field
and a `case` field. The replay flag wants bare cases, and it refuses a file
that holds the same program twice. This unwraps and deduplicates:

```
node -e '
const fs=require("fs");
const c=o=>Array.isArray(o)?o.map(c):o&&typeof o==="object"?Object.fromEntries(Object.keys(o).sort().map(k=>[k,c(o[k])])):o;
const seen=new Set, out=[];
for (const l of fs.readFileSync(process.argv[1],"utf8").split("\n")) {
  if (!l.trim()) continue;
  const r=JSON.parse(l), k=JSON.stringify(c(r.case));
  if (seen.has(k)) continue; seen.add(k); out.push(JSON.stringify(r.case));
}
fs.writeFileSync(process.argv[2], out.join("\n")+"\n");' crashes.ndjson crash-cases.ndjson
npm run --silent oracle -- --cases crash-cases.ndjson
```

Replaying all 7,833 takes about three and a half minutes, almost all of it
CLI restarts after each crash.

The twelve smallest crashers follow. All twelve reproduce on the current
binary. Save the block as a file and replay it with the cases flag; it runs in
seconds. The first is the smallest known: no inputs, fuel 1, a `switchAll` over
`map(fst)` over a `batchSync` whose source is a `map` over `of(unit)`.

```
{"ctx":[],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"of","ty":{"type":"unit"},"items":[{"type":"unitT","ty":{"type":"unit"}}]}}}}},"slots":[],"fuel":1}
{"ctx":[{"type":"nat"}],"exp":{"type":"mergeAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"input","ty":{"type":"nat"},"index":0}},"src":{"type":"input","ty":{"type":"nat"},"index":0}}}}},"slots":[{"type":"scripted","input":{"type":"cold","sync":[8,3,5],"async":[]}}],"fuel":10}
{"ctx":[],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"mu","ty":{"type":"obs","elem":{"type":"nat"}},"body":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"of","ty":{"type":"nat"},"items":[{"type":"natT","ty":{"type":"nat"},"val":8}]}}}}}},"slots":[],"fuel":3}
{"ctx":[],"exp":{"type":"exhaustAll","ty":{"type":"nat"},"src":{"type":"mu","ty":{"type":"obs","elem":{"type":"nat"}},"body":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"of","ty":{"type":"bool"},"items":[{"type":"boolT","ty":{"type":"bool"},"val":false}]}}}}}},"slots":[],"fuel":3}
{"ctx":[],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"mint","ty":{"type":"obs","elem":{"type":"nat"}},"body":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"of","ty":{"type":"bool"},"items":[{"type":"boolT","ty":{"type":"bool"},"val":true}]}}}}}},"slots":[],"fuel":5}
{"ctx":[{"type":"nat"}],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"input","ty":{"type":"nat"},"index":0}},"src":{"type":"input","ty":{"type":"nat"},"index":0}}}}},"slots":[{"type":"scripted","input":{"type":"cold","sync":[8,5,3],"async":[{"wait":2,"val":2},{"wait":1,"val":0}]}}],"fuel":6}
{"ctx":[],"exp":{"type":"take","ty":{"type":"nat"},"count":{"type":"natT","ty":{"type":"nat"},"val":1},"src":{"type":"exhaustAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"of","ty":{"type":"nat"},"items":[{"type":"natT","ty":{"type":"nat"},"val":0}]}}}}}},"slots":[],"fuel":6}
{"ctx":[{"type":"nat"}],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"mint","ty":{"type":"obs","elem":{"type":"nat"}},"body":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"empty","ty":{"type":"nat"}}},"src":{"type":"input","ty":{"type":"nat"},"index":0}}}}}},"slots":[{"type":"scripted","input":{"type":"cold","sync":[0,1],"async":[]}}],"fuel":9}
{"ctx":[],"exp":{"type":"mergeAll","ty":{"type":"unit"},"limit":3,"src":{"type":"map","ty":{"type":"obs","elem":{"type":"unit"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"unit"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"unit"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"unit"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"unit"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"unit"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"unit"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"unit"}},"exp":{"type":"of","ty":{"type":"unit"},"items":[{"type":"unitT","ty":{"type":"unit"}},{"type":"unitT","ty":{"type":"unit"}}]}},"src":{"type":"of","ty":{"type":"bool"},"items":[{"type":"boolT","ty":{"type":"bool"},"val":true}]}}}}},"slots":[],"fuel":9}
{"ctx":[{"type":"nat"}],"exp":{"type":"switchAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"input","ty":{"type":"nat"},"index":0}},"src":{"type":"mu","ty":{"type":"nat"},"body":{"type":"input","ty":{"type":"nat"},"index":0}}}}}},"slots":[{"type":"scripted","input":{"type":"cold","sync":[1,4],"async":[{"wait":1,"val":2}]}}],"fuel":7}
{"ctx":[],"exp":{"type":"defer","ty":{"type":"nat"},"body":{"type":"exhaustAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"of","ty":{"type":"nat"},"items":[]}},"src":{"type":"of","ty":{"type":"bool"},"items":[{"type":"boolT","ty":{"type":"bool"},"val":false},{"type":"boolT","ty":{"type":"bool"},"val":false}]}}}}}},"slots":[],"fuel":5}
{"ctx":[{"type":"nat"}],"exp":{"type":"defer","ty":{"type":"nat"},"body":{"type":"mergeAll","ty":{"type":"nat"},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"fstT","ty":{"type":"obs","elem":{"type":"nat"}},"pair":{"type":"varT","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"index":0}},"src":{"type":"batchSync","ty":{"type":"prod","fst":{"type":"obs","elem":{"type":"nat"}},"snd":{"type":"list","elem":{"type":"obs","elem":{"type":"nat"}}}},"src":{"type":"map","ty":{"type":"obs","elem":{"type":"nat"}},"fn":{"type":"strmT","ty":{"type":"obs","elem":{"type":"nat"}},"exp":{"type":"input","ty":{"type":"nat"},"index":0}},"src":{"type":"input","ty":{"type":"nat"},"index":0}}}}}},"slots":[{"type":"scripted","input":{"type":"cold","sync":[7,8],"async":[{"wait":1,"val":5}]}}],"fuel":7}
```

## What this session fixed, and why

- **The hang was pattern-`let` duplication, not a semantic stall.** An Agda
  pattern `let` over a tuple result is substitution, so each projected field is
  a fresh copy of the whole call. GHC shares copies within one clause but not
  across the drain recursion, which runs `mergeAllDrain!`, `inner!`,
  `innerFinish!`, `finishDrain!` and back. A nested limited flattener ran its
  drain exponentially in the lane depth. Every such site in Reducible is now a
  `with`. The rule and its reason are in the header above `reducible`. It is
  pinned as `typescript/cases/evaluator-stalls-under-a-limited-flattener.ndjson`.
- **A real double-completion bug.** A flattener's finish that drained a queued
  inner which ended synchronously reported completion twice: once through that
  inner's own finish, and once from the drained state. The frame above folded
  the end twice, and an enclosing limited flattener drained twice. rxjs's
  `mergeInternals` has the same double check, but its `complete` is idempotent.
  The finish rule `finish-all-drain` in `Rx/Evaluator/Domain.agda` now reports
  the end only when the queue was empty when the finish ran. Pinned as
  `typescript/cases/completion-crosses-the-exit-frame-twice.ndjson`.
- **A harness carrier bug, not an evaluator one.** A `scan` squaring its
  accumulator reached 5^64. rxjs rounded a double at every step, while the Agda
  side computed exactly and `JSON.parse` rounded once. TypeScript `Val` now
  carries nats as `bigint`. `toVal` in `typescript/src/exp.ts` converts at the
  corpus boundary, the bridge reads the CLI's digits through a JSON reviver, and
  both sides render through `showValues`. Pinned as
  `typescript/cases/nats-are-exact.ndjson`.
- **The bridge hands one CLI process at most 500 rows.** Before, a restart
  after a crash re-sent every remaining row, which was quadratic on a crash-heavy
  file and looked like a hang.

## Agda syntax facts learned in the `with` rewrite

- An ellipsis clause after a nested `with` binds to the innermost `with`. A
  sibling clause after a nested group must spell out its full left-hand side,
  or come first.
- `with (let … in call)` works. Keep a cheap `let` inside the scrutinee when its
  projection appears in the derivation's type, such as a wrap or a node lookup.
  Abstracting it loses the definitional equation the derivation is stated
  against.
- `in eq` variables stay usable in clauses that spell out the full left-hand
  side, and copattern clauses can use `with` under `--guardedness`.
- `make agda-dev` stubs multi-member blocks, so only a full build checks
  termination. `cli-build` is a full check.

## Left undone

- **`stuck-hop` itself.** The top leg of PROOF-STATE's Tier 1 roadmap is
  "PEEL EVERY FRAME, NOT ONLY THE EXIT FRAME": name the parent's predicate
  through the path index so every transformer arm returns its parent's
  successor. The leg after it turns the runtime certification into a proof,
  where the continuation or the state carries which cell it certifies as an
  index. Both are design work, which CLAUDE.md says the design session keeps.
- **`stuck-finish` was never reached**, nonempty queues included. It stays
  FALSITY because a sweep that never reaches a branch is not evidence about
  it.
- **Pattern-`let`s outside the drain path are untouched.** In
  `Rx/Evaluator/Builder.agda` they are in `chainStep!`, `cascadeGo!`,
  `cascade!`, `drain!` and `evaluate!`. In `Rx/Evaluator.agda` they are in
  `takeVals` and `switchKill`. Reducible keeps a few that are not on a
  recursion: `T-if`, `redScanDispatch`, the two single-field recomputes in
  `scanRP` and `batchRP`, the `stuck-hop` call in `red-hop`, and the ones in
  `dispatchShare!`, `shareWalk!` and `shareGo!`. None was measured to matter,
  since the 1.5M sweep has no timeouts.

## Traps met

- `pkill -f <pattern>` inside a Bash call matches the calling shell's own
  command line and kills it. Find the process id with `ps` first.
- The sweep's 22 MB crash file lived in a session scratchpad and is gone with
  that container. The seed list replaces it.
- The CLI binary is `agda/_cli/Main`. Set `AGDA_CLI_BIN` to compare against a
  saved copy of an older build.
