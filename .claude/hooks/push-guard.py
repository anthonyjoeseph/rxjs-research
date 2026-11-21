#!/usr/bin/env python3
# PreToolUse hook (Bash): refuse a `git push` while a Gate run is live on the
# branch.  A push to a PR cancels the run in flight, and a cancelled run saves
# no interface cache, so the next run starts colder (Anthony: block the push,
# not the commit).  Override, deliberately and visibly: GATE_CANCEL_OK=1 git push …
# Fails OPEN: if GitHub cannot be asked, the push goes through with a warning.
import json, re, subprocess, sys, urllib.request
from datetime import datetime, timezone

LIVE = {"queued", "in_progress", "waiting", "requested", "pending"}
STALE_MIN = 95  # past the gate job's timeout-minutes: a dead runner's zombie run

def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True).stdout.strip()

cmd = json.load(sys.stdin).get("tool_input", {}).get("command", "")
# `git` at a command position (start, or after ; & | newline, past any
# VAR=value prefixes), so a command merely mentioning "git push" passes.
PUSH = r"(?:^|[;&|\n])\s*(?:\w+=\S*\s+)*git\b(?:\s+-\S+(?:\s+\S+)?)*\s+push\b"
if not re.search(PUSH, cmd) or "GATE_CANCEL_OK=1" in cmd:
    sys.exit(0)

m = re.search(r"github\.com[/:]([^/]+/[^/.]+)", git("remote", "get-url", "origin"))
branch = git("rev-parse", "--abbrev-ref", "HEAD")
if not m or not branch:
    sys.exit(0)

url = (f"https://api.github.com/repos/{m.group(1)}/actions/workflows/gate.yml/runs"
       f"?branch={branch}&per_page=20")
try:
    req = urllib.request.Request(url, headers={"Accept": "application/vnd.github+json",
                                               "User-Agent": "push-guard"})
    runs = json.load(urllib.request.urlopen(req, timeout=10))["workflow_runs"]
except Exception as e:
    print(f"push-guard: could not ask GitHub ({e}); letting the push through", file=sys.stderr)
    sys.exit(0)

now = datetime.now(timezone.utc)
live = []
for r in runs:
    if r["status"] not in LIVE:
        continue
    started = datetime.fromisoformat(r["run_started_at"].replace("Z", "+00:00"))
    mins = (now - started).total_seconds() / 60
    if mins < STALE_MIN:
        live.append((r, mins))

if not live:
    sys.exit(0)

lines = [f"  Gate #{r['run_number']} ({r['event']}) on {r['head_sha'][:8]}: {r['status']}, "
         f"{mins:.0f} min in — {r['html_url']}" for r, mins in live]
print("push-guard: a Gate run is live on " + branch + "; a push cancels it.\n"
      + "\n".join(lines)
      + "\nKeep committing locally and push when it finishes. To cancel it on purpose: "
        "GATE_CANCEL_OK=1 git push …", file=sys.stderr)
sys.exit(2)
