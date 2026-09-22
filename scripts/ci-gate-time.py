#!/usr/bin/env python3
"""What the gate cost on CI, fetched rather than recorded.

A CI timing is a receipt about a machine nobody here owns, on a cache state
nobody here controls.  Written into `typecheck-performance-numbers.md` it
becomes the one kind of number that cannot be re-measured to check it: the
runner image moves, the cache key rotates, and the figure stays.  So the
file carries this command instead of the numbers, and the numbers come from
the runs themselves, which are the only place they were ever true.

Reads the most recent SUCCESSFUL `Gate` runs and prints, per run, how long
the `make gate` step took and whether the Agda interface cache was restored
-- which is the whole spread, and the reason a single figure would lie.

Auth: `GH_TOKEN` or `GITHUB_TOKEN` if set, otherwise `gh auth token`.  The
API is readable without either on a public repository, at a lower rate
limit.
"""

import json
import os
import subprocess
import sys
import urllib.error
import urllib.request
from datetime import datetime

REPO = "anthonyjoeseph/rxjs-research"
WORKFLOW = "gate.yml"
JOB = "gate"
STEP = "make gate"
CACHE_STEP = "Cache Agda interfaces"


def token():
    for var in ("GH_TOKEN", "GITHUB_TOKEN"):
        if os.environ.get(var):
            return os.environ[var]
    try:
        out = subprocess.run(
            ["gh", "auth", "token"], capture_output=True, text=True, timeout=10
        )
        if out.returncode == 0 and out.stdout.strip():
            return out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def api(path):
    req = urllib.request.Request(
        f"https://api.github.com{path}",
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "rxjs-research-ci-gate-time",
            **({"Authorization": f"Bearer {token()}"} if token() else {}),
        },
    )
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def secs(a, b):
    if not a or not b:
        return None
    fmt = "%Y-%m-%dT%H:%M:%SZ"
    return int((datetime.strptime(b, fmt) - datetime.strptime(a, fmt)).total_seconds())


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    try:
        runs = api(
            f"/repos/{REPO}/actions/workflows/{WORKFLOW}/runs"
            f"?status=success&per_page={limit}"
        )["workflow_runs"]
    except urllib.error.HTTPError as e:
        print(f"ci-gate-time: GitHub API said {e.code} {e.reason}", file=sys.stderr)
        print("  set GH_TOKEN, or `gh auth login`, and try again", file=sys.stderr)
        return 1
    except (urllib.error.URLError, OSError) as e:
        print(f"ci-gate-time: could not reach GitHub ({e})", file=sys.stderr)
        return 1

    if not runs:
        print(f"ci-gate-time: no successful `{WORKFLOW}` run to read")
        return 0

    print(f"`{STEP}` on the {len(runs)} most recent GREEN Gate runs:\n")
    print(f"{'branch':<34} {'cache':<7} {STEP:>10}   run")
    for run in runs:
        jobs = api(f"/repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=40")["jobs"]
        job = next((j for j in jobs if j["name"] == JOB), None)
        if job is None:
            continue
        steps = {s["name"]: s for s in job.get("steps", [])}
        gate = steps.get(STEP)
        if gate is None:
            continue
        el = secs(gate.get("started_at"), gate.get("completed_at"))
        cache = steps.get(CACHE_STEP, {}).get("conclusion", "?")
        warm = {"success": "warm", "skipped": "n/a"}.get(cache, cache)
        print(
            f"{run['head_branch'][:33]:<34} {warm:<7} "
            f"{(str(el) + ' s') if el is not None else '?':>10}   "
            f"{run['html_url']}"
        )
    print(
        "\nA warm run restored an interface snapshot Agda still accepts; a cold one\n"
        "did not, and is measuring that snapshot's staleness rather than the tower.\n"
        "Read the SPREAD, not any single row -- which is why this is fetched."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
