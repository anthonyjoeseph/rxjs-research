#!/usr/bin/env python3
"""PUSHES THE LEDGER'S SHAPE TO A PHONE AT THE MOMENT IT IS ABOUT TO MOVE.

A gate run is the one point where the tree is known-good and a commit is next,
so it is the only place a census is worth sending: any earlier and the numbers
describe a tree that is still being edited.

WHY THIS COMPUTES THE COUNTS RATHER THAN READING THEM.  PROOF-STATE.md carries
no aggregates on purpose -- a hand-typed total is true when written and wrong
later, with nothing checking it.  Every number here is derived from the roadmap
and the postulate ledger at send time, so it cannot be stale; nothing is stored
and no file is written.

The topic is read from NTFY_TOPIC, falling back to `.ntfy-topic` at the repo
root.  Absent both, this exits zero having sent nothing -- a notification is a
convenience and may never fail a gate.
"""
import json
import os
import re
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

CLASSES = cr.CLASSES
DURABLE_KINDS = cr.DURABLE_KINDS

# how a marker kind reads when it is being COUNTED rather than named.  The
# roadmap's field is a vocabulary and stays upper-case there; a total is
# prose and reads as one.
EVID_WORD = {
    "REFUTED": ("refutation", "refutations"),
    "DEAD ROUTE": ("dead route", "dead routes"),
    "TWIN": ("twin", "twins"),
    "PROBED": ("probe", "probes"),
    "RECOVERY": ("recovery", "recoveries"),
}


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


def census(live):
    """-> [(tier, {risk class: rows}, {marker kind: markers})]

    The evidence half is summed from the postulates' OWN HEADERS, by the same
    reader the gate's evidence check uses -- not from the roadmap's fields.
    Both say the same thing today because `roadmap-check` fails when they
    disagree, and reading the headers is what makes that true rather than
    assumed.  Markers are counted with multiplicity: a row carrying
    `REFUTED×4` contributes four.
    """
    tiers = cr.parse(ROOT / "PROOF-STATE.md")
    cen = cr.census(ROOT, live)
    out = []
    for name, rows, _pre, _legs in tiers:
        counts = {}
        evid = {}
        for label, cls, _ln, _cost in rows:
            if not cls:
                continue
            counts[cls] = counts.get(cls, 0) + 1
            for k, v in cr.row_evidence(label, cen).items():
                evid[k] = evid.get(k, 0) + v
        out.append((name, counts, evid))
    return out


def postulate_counts(rows, live):
    """-> {risk class: how many LIVE POSTULATES the tier's rows name}

    Rows and postulates are not the same census and the difference is not
    cosmetic: one row routinely heads a family, so a row count reads the tier
    as smaller than the ledger it stands for.  The class is the row's, since
    that is where a class is declared, and a name is counted once however many
    rows reach it.
    """
    out = {}
    for label, cls, _ln, _cost in rows:
        if not cls:
            continue
        seen = out.setdefault(cls, set())
        for group in cr.head_groups(label):
            for name in group:
                if "*" in name:
                    seen.update(n for n in live if re.fullmatch(
                        re.escape(name).replace(r"\*", ".*"), n))
                elif name in live:
                    seen.add(name)
    return {k: len(v) for k, v in out.items()}


def roadmap(tier):
    """-> the tier's BIG PICTURE ROADMAP, verbatim.

    Read from the file rather than from the parser's leg labels, because the
    labels are the leg TITLES and the schedule is the prose under them -- the
    titles alone say which three groups are next and none of why.
    """
    lines = (ROOT / "PROOF-STATE.md").read_text().splitlines()
    out, state = [], 0
    for ln in lines:
        if state == 0:
            if ln.startswith("## Tier ") and ln[8:].startswith(tier):
                state = 1
        elif state == 1:
            if ln.startswith("### Big picture"):
                state = 2
        else:
            if ln.startswith("### ") or ln.startswith("## "):
                break
            out.append(ln)
    while out and not out[-1].strip():
        out.pop()
    return out


def fmt_counts(counts):
    parts = [f"{counts[c]} {c.lower()}" for c in CLASSES if counts.get(c)]
    return ", ".join(parts) if parts else "clear"


def fmt_evid(evid):
    parts = []
    for k in DURABLE_KINDS:
        n = evid.get(k, 0)
        if n:
            one, many = EVID_WORD[k]
            parts.append(f"{n} {one if n == 1 else many}")
    return ", ".join(parts) if parts else "no evidence"


def main():
    verdict = sys.argv[1] if len(sys.argv) > 1 else "GATE"
    path = sys.argv[2] if len(sys.argv) > 2 else ""

    live_names = cr.live_postulates(ROOT) or []
    tiers = census(live_names)
    open_tiers = [(n, c, e) for n, c, e in tiers if sum(c.values())]
    lowest = open_tiers[0] if open_tiers else None

    live = len(live_names)
    total = {}
    total_evid = {}
    for _n, c, e in tiers:
        for k, v in c.items():
            total[k] = total.get(k, 0) + v
        for k, v in e.items():
            total_evid[k] = total_evid.get(k, 0) + v

    branch = git("rev-parse", "--abbrev-ref", "HEAD", default="?")
    head = git("log", "-1", "--format=%h %s", default="?")
    dirty = git("status", "--porcelain", default="")
    nfiles = len([l for l in dirty.splitlines() if l.strip()])

    lines = []
    if lowest:
        name, counts, evid = lowest
        head_rows = [r for r in cr.parse(ROOT / "PROOF-STATE.md")
                     if r[0] == name][0][1]
        pc = postulate_counts(head_rows, set(live_names))
        lines.append(f"Tier {name} is the lowest open — {fmt_counts(pc)}")
        lines.append(f"across {fmt_counts(counts)} on the roadmap")
        lines.append(f"standing on {fmt_evid(evid)}")
        lines.append("")
        lines.extend(roadmap(name))
    else:
        lines.append("no tier has a classed row left")

    lines.append("")
    for name, counts, evid in tiers:
        lines.append(f"  tier {name}: {fmt_counts(counts)}")
        lines.append(f"    evidence: {fmt_evid(evid)}")
    lines.append("")
    lines.append(f"{live} live postulate(s) across the tree"
                 f" — {fmt_counts(total)} on the roadmap")
    lines.append(f"evidence standing under them: {fmt_evid(total_evid)}")
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
