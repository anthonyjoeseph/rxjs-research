# Compiled probes — `make qc-<statement>` and `QC_DRAW`

The typechecker probe (`agda/evidence/probed/`) pins ONE program per row by
`refl` and costs minutes to hours a shape. The compiled probe is the
high-volume one: `CLI/QuickCheck.agda` built by GHC, drawing hundreds of
programs a minute and deciding one statement's two sides on each run.
It is EVIDENCE, never a proof's dependency, and it carries no `PROBED:`
receipt — nothing can fingerprint a binary. A green that reached a row's
risky region is a FINDING named with the statement, the region and the seed
range; a red is a CANDIDATE until its paste row typechecks as a refutation.

## Running one

```
make qc-store QC='SEED RUNS DEPTH' QC_FUEL=30 QC_BUDGET=600
```

One target per statement (`make help` lists them); `qc-fast QC_STMT=<n>`
names one by number. Every case streams to `agda/_oracle/qc.stream` as it is
decided, so a sweep the budget kills still says what it decided. Builds go
through `make bg`, one at a time, like any other.

## Aiming the draw — `QC_DRAW`

A uniform draw rarely lands in the region one postulate is about. `QC_DRAW`
is one JSON object on the binary's second stdin line, and it AIMS the draw by
weighting the arms the generator picks between; it never filters what was
drawn, except by `reach`.

```
make qc-store QC='1 100 4' QC_FUEL=30 \
  QC_DRAW='{"exp":[1,1,0,0,4,4,4,4,1,1,0,0,4],"reach":["flatten","defer"]}'
```

- A knob is one weight per arm; a zero arm is never taken. An absent knob is
  the uniform pick and consumes exactly the randomness it always did, so an
  unset `QC_DRAW` draws, seed for seed, the programs it always drew.
- `reach` lists former tags (the census's names) every case must carry.
  A case spends up to `tries` draws (default 1000) finding one; a case that
  finds none is reported `unreached`, counted undecided, and not run.
  Every route naming a case by index (`SHOW-AT`, `RUN-AT`, `SIDE`) spends the
  same draws, so a case number names one program under one `QC_DRAW`.
- An unknown key, a wrong arm count, an all-zero knob or an unknown tag is
  refused with `restriction: …` and nothing runs — a misspelt knob read as
  "unrestricted" would be a sweep aimed somewhere else that says it was aimed
  here.

### The knobs, arm by arm

| Knob | Arms |
| --- | --- |
| `exp` (13) | 0–1 leaf · 2 map · 3 scan · 4 mergeAll · 5 bounded mergeAll (limit 1–3) · 6 switchAll · 7 exhaustAll · 8 μ · 9 defer · 10 take · 11 takeWhile · 12 flatten over a fan step |
| `spineD` (10), past a μ's defer | 0 the var · 1 map · 2 scan · 3 mergeAll · 4 bounded mergeAll · 5 switchAll · 6 flatten over a fan step · 7 take · 8 takeWhile · 9 exhaustAll |
| `spineG` (10), before it | 0–1 the defer · 2 map · 3 scan · 4 mergeAll · 5 switchAll · 6 flatten over a fan step · 7 take · 8 takeWhile · 9 exhaustAll |
| `op` (5), a flatten's policy | 0 merge · 1 bounded merge · 2 switch · 3 exhaust · 4 merge |
| `fan` (9), a flatten's step | lane: 0 empty · 1 `[x,x]` · 2 `[x,k]` · 3 filtered · 4 `[x]`; 5 nothing · 6 filtered echo · 7 echo and lane `[k]` · 8 echo |
| `script` (4), slot zero | 0 hot, one arrival · 1 hot, two · 2 cold, one sync value and one arrival · 3 cold, two arrivals |
| `slot` (4), slot one | 0 forwards slot zero · 1 empty · 2 one value · 3 two values |
| `leaf` (3) | 0 a slot · 1 empty · 2 two values |
| `obs` (4), a stream of streams | 0 a fold at observable type (leaf level only, else a list) · 1–3 a literal list of inners |

Depth bounds every spine: at depth zero an `exp` is a leaf whatever the
weights say, so a must-have former deeper than the depth allows comes back
`unreached`.

## Reading a sweep

The summary's census counts formers per case, and each streamed case names
its own; a region claim cites the census, not the weights. Before trusting a
green on a new decider, break it on purpose (misread one index) and confirm it
goes red: a decider that cannot fail is a probe that lies green.
