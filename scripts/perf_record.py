#!/usr/bin/env python3
"""Record a measured typecheck timing into typecheck-performance-numbers.md.

WHY BOTH `last` AND `best` ARE KEPT, and why `best` is the one to trust.
Every way a timing here can be distorted runs in the SLOW direction: a rebuilding
dependency means you measured the dependency, a concurrent heavyweight check means
you measured contention, a cold interface means you measured deserialization.  None
of them can make a module look FASTER than it is.  So the minimum over many
observations converges on the real coherent-cache cost, while the latest
observation is whatever happened to be true of the last run's cache state.  Read
`best`; treat a `last` far above it as a statement about the cache, not the code.

That asymmetry is what makes automatic recording safe at all.  A naive "overwrite
with the newest number" would have written 357s for Verify-Well-Formed/Part1 and
904.6s for Main, both off by ~50x, because that is what the last run said.

WRITES ARE SUPPRESSED UNLESS SOMETHING ACTUALLY CHANGED.  A build that reproduces
its own recorded numbers leaves the file byte-identical, so a green run does not
dirty the tree and does not produce a diff to review.  A row is rewritten only on
a new best, or when `last` moves by more than NOISE.

EVERY ROW IS TAGGED BY ENVIRONMENT (`scripts/detect_env.py`), AND THAT IS NOT
COSMETIC.  A number from a faster or slower machine is not noise around the
same truth, it is a measurement of a DIFFERENT machine -- so before this tag
existed, a real, fast `agda-dev Main.agda` run from a cloud container silently
overwrote a laptop's own `>45 s` budget-kill floor for the identical target,
because the two were the same key.  Nothing said the two numbers came from
different places; the file just looked like Main.agda had gotten faster.
Every row lives under its environment's own section and `best` is tracked
per-environment, so a cloud container can never again retire a laptop's
number, or the reverse.

ONLY GREEN RUNS ARE RECORDED, WITH ONE EXCEPTION THAT IS THE SAME ARGUMENT
RATHER THAN A HOLE IN IT.  A timing from a failed check measures how long it took
to FAIL, which is not a cost anyone wants to plan against.  A timing from a check
killed by the BUDGET measures no such thing: nothing went wrong, the clock simply
ran out, so the number is a LOWER BOUND on the real cost and it is distorted in
the slow direction like every other observation here.  Dropping it is the one way
this file can state a number that is not merely stale but inverted -- a module
that used to be fast and now cannot finish keeps its old row and reports the old
figure, with nothing anywhere saying otherwise.  So a timeout updates `last` and
sets a floor flag that renders it as `>Ns`, and it never touches `best`, which is
still a real measurement of a run that really finished.
"""

from __future__ import annotations

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import detect_env  # noqa: E402  (needs the path fixup above)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOC = os.path.join(ROOT, "typecheck-performance-numbers.md")

BEGIN = "<!-- AUTO:BEGIN -- maintained by scripts/perf_record.py, do not hand-edit -->"
END = "<!-- AUTO:END -->"
PAYLOAD = re.compile(r"<!-- AUTO:DATA\s+(\{.*?\})\s+-->", re.S)

# Relative change in `last` below which the file is left alone.  Timings jitter by
# a few percent between identical runs; rewriting on that would mean every build
# produced a diff, and a file that always has a diff stops being read.
NOISE = 0.15

# The composite key is "<env>|<target>".  "|" never appears in a target name
# (those are make-target-ish strings: file paths, spaces, parens), so it is
# an unambiguous split.  A key with no recognised env prefix predates this
# tagging entirely -- every row recorded before it existed came from the one
# machine this campaign ran on before a second one joined, so it migrates to
# `local` once, on load, rather than being dropped or misfiled.
KEY = re.compile(r"^(" + "|".join(detect_env.ENVS) + r")\|(.*)$", re.S)


def _load(text: str) -> dict:
    m = PAYLOAD.search(text)
    raw = json.loads(m.group(1)) if m else {}
    data: dict = {}
    for key, row in raw.items():
        km = KEY.match(key)
        if km:
            data[key] = row
        else:
            data[f"{detect_env.LOCAL}|{key}"] = row
    return data


def _render(data: dict) -> str:
    out = [
        BEGIN,
        "",
        "*Recorded automatically by the build, one section per environment"
        " (`scripts/detect_env.py`). `best` is the number to trust — see"
        " `scripts/perf_record.py` for why.*",
        "",
    ]
    for env in detect_env.ENVS:
        rows = sorted(
            ((KEY.match(k).group(2), r) for k, r in data.items()
             if KEY.match(k).group(1) == env),
            key=lambda kv: -kv[1]["best"])
        if not rows:
            continue
        out += [f"### {detect_env.LABELS[env]}", "",
                "| Target | Best | Last | Runs |", "|---|---|---|---|"]
        for name, r in rows:
            last = (f">{r['last']:.0f} s" if r.get("floor")
                    else f"{r['last']:.1f} s")
            out.append(f"| `{name}` | **{r['best']:.1f} s** | {last} | {r['runs']} |")
        out.append("")
    out += [f"<!-- AUTO:DATA {json.dumps(data, sort_keys=True)} -->", "", END]
    return "\n".join(out)


def record(target: str, seconds: float, floor: bool = False, env: str | None = None) -> bool:
    """Merge one observation.  Returns True if the file was rewritten.

    `floor` marks an observation cut short by the caller's budget rather than
    completed, so it bounds the cost from below and may not enter `best`.
    `env` defaults to the environment this process is actually running in
    (`scripts/detect_env.py`) -- callers never need to pass it, and every
    existing call site still works unchanged.
    """
    if not os.path.exists(DOC):
        return False
    text = open(DOC).read()
    if BEGIN not in text or END not in text:
        return False

    key = f"{env or detect_env.detect_env()}|{target}"
    data = _load(text)
    row = data.get(key)
    if row is None:
        if floor:
            # No completed run to draw a `best` from, and a floor may not become
            # one: it would understate a module nobody has ever seen finish.
            data[key] = {"best": round(seconds, 1), "last": round(seconds, 1),
                        "runs": 1, "floor": True}
        else:
            data[key] = {"best": round(seconds, 1), "last": round(seconds, 1),
                        "runs": 1}
        changed = True
    else:
        row["runs"] += 1
        prev_last, prev_best = row["last"], row["best"]
        prev_floor = row.get("floor", False)
        row["last"] = round(seconds, 1)
        if floor:
            row["floor"] = True
        else:
            row.pop("floor", None)
            row["best"] = round(min(prev_best, seconds), 1)
        changed = (row["best"] < prev_best) or (row.get("floor", False) != prev_floor) or (
            prev_last > 0 and abs(seconds - prev_last) / prev_last > NOISE
        )
        # `runs` alone is not worth a rewrite; restore it if nothing else moved.
        if not changed:
            row["runs"] -= 1
            row["last"] = prev_last

    if not changed:
        return False

    head, rest = text.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    tmp = DOC + ".tmp"
    with open(tmp, "w") as f:
        f.write(head + _render(data) + tail)
    os.replace(tmp, DOC)          # atomic: a killed build cannot truncate the doc
    return True


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: perf_record.py <target> <seconds>", file=sys.stderr)
        return 2
    try:
        secs = float(argv[2])
    except ValueError:
        print(f"perf_record: not a number: {argv[2]!r}", file=sys.stderr)
        return 2
    if secs <= 0:
        return 0
    record(argv[1], secs)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
