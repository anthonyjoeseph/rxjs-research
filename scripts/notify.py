#!/usr/bin/env python3
"""PUSHES THE LEDGER'S SHAPE TO A PHONE AT THE MOMENT IT IS ABOUT TO MOVE.

A gate run is the one point where the tree is known-good and a commit is next,
so it is the only place a census is worth sending: any earlier and the numbers
describe a tree that is still being edited.

WHY THIS COMPUTES THE COUNTS RATHER THAN READING THEM.  PROOF-STATE.md carries
no aggregates on purpose -- a hand-typed total is true when written and wrong
later, with nothing checking it.  Every number here is derived from the groups'
members and the postulate ledger at send time, so it cannot be stale.

The topic is read from NTFY_TOPIC, falling back to `.ntfy-topic` at the repo
root.  Absent both, this exits zero having sent nothing -- a notification is a
convenience and may never fail a gate.
"""
import os
import pathlib
import subprocess
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import importlib.util

spec = importlib.util.spec_from_file_location(
    "check_roadmap", ROOT / "scripts" / "check-roadmap.py")
cr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cr)

def topic():
    t = os.environ.get("NTFY_TOPIC", "").strip()
    if t:
        return t
    f = ROOT / ".ntfy-topic"
    if f.exists():
        return f.read_text().strip()
    return ""


def git(*args, default=""):
    try:
        return subprocess.run(("git",) + args, cwd=ROOT, capture_output=True,
                              text=True, check=True).stdout.strip()
    except Exception:
        return default


def census(tiers, live):
    """-> [(tier, [(group title, live members)])] -- counted, never read."""
    return [(t.name, [(g.title, sum(1 for n in live
                                    if any(cr.matches(k, n) for k in g.tokens)))
                      for g in t.groups])
            for t in tiers]


def main():
    verdict = sys.argv[1] if len(sys.argv) > 1 else "GATE"
    path = sys.argv[2] if len(sys.argv) > 2 else ""

    live_names = cr.live_postulates() or []
    _pre, tiers, _problems = cr.parse(ROOT / "PROOF-STATE.md")
    cen = census(tiers, live_names)
    lowest = next((t for t in tiers if t.groups), None)

    branch = git("rev-parse", "--abbrev-ref", "HEAD", default="?")
    head = git("log", "-1", "--format=%h %s", default="?")
    dirty = git("status", "--porcelain", default="")
    nfiles = len([l for l in dirty.splitlines() if l.strip()])

    lines = []
    if lowest:
        top = lowest.groups[0]
        lines.append(f"Tier {lowest.name} is the lowest open — top group {top.title}")
        lines.append("")
        lines.extend(lowest.progress or ["(no progress recorded)"])
    else:
        lines.append("no tier has a group left")

    lines.append("")
    for name, groups in cen:
        for title, n in groups:
            lines.append(f"  tier {name}: {title} — {n} postulate(s)")
    lines.append("")
    lines.append(f"{len(live_names)} live postulate(s) across the tree")
    lines.append(f"{nfiles} file(s) uncommitted on {branch}")
    lines.append(f"HEAD {head}")
    if path:
        lines.append(f"log {path}")

    body = "\n".join(lines)
    t = topic()
    if not t:
        print("notify: no NTFY_TOPIC and no .ntfy-topic — nothing sent")
        print(body)
        return 0

    green = verdict.upper().startswith("GREEN")
    req = urllib.request.Request(
        f"https://ntfy.sh/{t}",
        data=body.encode("utf-8"),
        headers={
            "Title": f"gate {verdict} - about to commit",
            "Priority": "default" if green else "high",
            "Tags": "white_check_mark" if green else "x",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as r:
            r.read()
        print(f"notify: sent to ntfy.sh/{t}")
    except Exception as exc:
        print(f"notify: send failed ({exc}) — gate unaffected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
