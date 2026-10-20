#!/usr/bin/env python3
"""`make roadmap-check` — the gate on PROOF-STATE.md (and the dates in CLAUDE.md, docs/).

PROOF-STATE is a risk ledger: per tier, a one-line description, then a
`### Ledger` of GROUPS, each a `####` heading over one block -- the design issue
its postulates share, what would settle it -- closed by a `Members:` list of
backticked names.  The rules it lives by are CLAUDE.md's; this script checks the
half a machine can see:

- COVERAGE: every live postulate is a member of some group.
- ONE GROUP: no live postulate is a member of two.
- STALENESS: a member naming nothing live is removed (`--prune`, which `make
  roadmap-check` passes), and a group left with no members is deleted.
  Deleting a postulate costs nothing (Anthony).
- SHAPE: a group carries a `Members:` line and sits under a ledger; a tier has
  no subsection but its ledger.
- BUDGETS: on the file's preamble, each tier's description and each group's
  prose.  Names are free.
- NO DATES: in PROOF-STATE, CLAUDE.md and docs/*.md.

Member shorthand: `{a,b}` brace expansion and `*` globs.

Mechanics and rationale: docs/roadmap-check.md.
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

FILE_BUDGET = 300
TIER_BUDGET = 150
GROUP_BUDGET = 600

TIER_RE = re.compile(r"^##\s+Tier\s+(\S+)")
SUB_RE = re.compile(r"^###\s+(.*?)\s*$")
GROUP_RE = re.compile(r"^####\s+(.*?)\s*$")
MEMBERS_RE = re.compile(r"^\*{0,2}Members:\*{0,2}")
BACKTICK_RE = re.compile(r"`([^`]+)`")
BACKTICK_SPAN_RE = re.compile(r"`[^`]*`")

# Any ISO-ish or spelled date.  None of these files has a legitimate use for one.
DATE_RE = re.compile(
    r"\b(?:\d{4}-\d{2}-\d{2}"
    r"|(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{1,2},?\s+\d{4}"
    r"|\d{1,2}\s+(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{4})\b")
DATE_ONLY_FILES = ["CLAUDE.md"]
DATE_ONLY_GLOBS = ["docs/*.md"]


def prose_cost(lines):
    """Characters spent EXPLAINING — every backticked name is free."""
    text = " ".join(l.strip() for l in lines).replace("**", "")
    return len(re.sub(r"\s+", " ", BACKTICK_SPAN_RE.sub("", text)).strip())


class Group:
    def __init__(self, title, lineno):
        self.title, self.lineno = title, lineno
        self.prose = []          # explanation lines
        self.members = None      # (first, last) line index of the Members block
        self.tokens = []         # backticked member tokens, in order
        self.end = None          # line index one past the group's last line


class Tier:
    def __init__(self, name, lineno):
        self.name, self.lineno = name, lineno
        self.pre = []
        self.in_ledger = False
        self.groups = []


def parse(path):
    """-> (file preamble lines, [Tier], [(lineno, problem)])"""
    lines = path.read_text().splitlines()
    tiers, problems, file_pre = [], [], []
    tier = group = None
    section = None               # None | "ledger" | "other"
    in_members = False

    def close_group(i):
        nonlocal group
        if group is not None:
            group.end = i
            if group.members is None:
                problems.append((group.lineno,
                                 f"group `{group.title}` has no `Members:` line"))
        group = None

    for i, line in enumerate(lines):
        if line.startswith("# ") and tier is None:
            continue
        mt = TIER_RE.match(line)
        if mt:
            close_group(i)
            tier = Tier(mt.group(1), i + 1)
            tiers.append(tier)
            section, in_members = None, False
            continue
        if tier is None:
            if line.strip():
                file_pre.append(line)
            continue
        ms = SUB_RE.match(line)
        if ms and not GROUP_RE.match(line):
            close_group(i)
            if ms.group(1).lower() == "ledger":
                section = "ledger"
                tier.in_ledger = True
            else:
                section = "other"
                problems.append((i + 1, f"`### {ms.group(1)}`: a tier's only subsection is its `### Ledger`"))
            in_members = False
            continue
        mg = GROUP_RE.match(line)
        if mg:
            close_group(i)
            if section != "ledger":
                problems.append((i + 1, f"group `{mg.group(1)}` is not under a `### Ledger`"))
            group = Group(mg.group(1), i + 1)
            tier.groups.append(group)
            in_members = False
            continue
        if group is not None:
            if MEMBERS_RE.match(line):
                in_members = True
                group.members = [i, i + 1]
                group.tokens += BACKTICK_RE.findall(line)
            elif in_members and line.strip():
                group.members[1] = i + 1
                group.tokens += BACKTICK_RE.findall(line)
            else:
                in_members = False
                if line.strip():
                    group.prose.append(line)
            continue
        if not line.strip():
            continue
        if section is None:
            tier.pre.append(line)
    close_group(len(lines))
    return file_pre, tiers, problems


def expand(tok):
    mb = re.match(r"^(.*)\{([^}]*)\}(.*)$", tok)
    if mb:
        return [mb.group(1) + a.strip() + mb.group(3) for a in mb.group(2).split(",")]
    return [tok]


def matches(tok, name):
    for t in expand(tok):
        if t == name or ("*" in t and re.fullmatch(re.escape(t).replace(r"\*", ".*"), name)):
            return True
    return False


def live_postulates(ledger=None):
    """-> the live-postulate names, or None if the ledger cannot be read."""
    if ledger:
        text = pathlib.Path(ledger).read_text()
    else:
        try:
            r = subprocess.run(["scripts/check-wiring.py", "--postulates"],
                               cwd=ROOT, capture_output=True, text=True, timeout=180)
        except Exception:
            return None
        if r.returncode != 0:
            return None
        text = r.stdout
    names = [ln.split()[0] for ln in text.splitlines()
             if ".agda:" in ln and not ln.startswith("--")]
    return names or None


def group_of(tiers):
    """-> [(tier, group, token)] over every member token."""
    return [(t, g, k) for t in tiers for g in t.groups for k in g.tokens]


def prune(path, tiers, live):
    """Drop member tokens naming nothing live, and groups left empty.
    -> [(group title, token)] removed."""
    lines = path.read_text().splitlines()
    removed, cuts = [], []        # cuts: (start, end, replacement lines)
    for t in tiers:
        for g in t.groups:
            if g.members is None:
                continue
            keep = [k for k in g.tokens if any(matches(k, n) for n in live)]
            gone = [k for k in g.tokens if k not in keep]
            if not gone:
                continue
            removed += [(g.title, k) for k in gone]
            if keep:
                cuts.append((g.members[0], g.members[1], wrap_members(keep)))
            else:
                end = g.end
                while end > g.lineno and not lines[end - 1].strip():
                    end -= 1
                start = g.lineno - 1
                # take the blank line after the group with it
                while end < len(lines) and not lines[end].strip():
                    end += 1
                cuts.append((start, end, []))
    for start, end, repl in sorted(cuts, reverse=True):
        lines[start:end] = repl
    if removed:
        path.write_text("\n".join(lines).rstrip("\n") + "\n")
    return removed


def wrap_members(tokens, width=79):
    out, cur = [], "Members:"
    for i, k in enumerate(tokens):
        piece = f"`{k}`" + ("," if i < len(tokens) - 1 else ".")
        if len(cur) + 1 + len(piece) > width:
            out.append(cur)
            cur = piece
        else:
            cur += " " + piece
    out.append(cur)
    return out


def dated_lines(path):
    return [(i, m.group(0)) for i, line in enumerate(path.read_text().splitlines(), 1)
            for m in [DATE_RE.search(line)] if m]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="roadmap to check (default: PROOF-STATE.md)")
    ap.add_argument("--ledger", help="file of live postulate names (default: the real ledger)")
    ap.add_argument("--prune", action="store_true",
                    help="remove members naming nothing live, and groups left empty")
    ap.add_argument("--dates-only", action="append", default=None, metavar="PATH",
                    help="files held to the date check alone (default: CLAUDE.md, docs/*.md)")
    args = ap.parse_args()

    path = pathlib.Path(args.file) if args.file else ROOT / "PROOF-STATE.md"
    fail = False

    file_pre, tiers, problems = parse(path)
    live = live_postulates(args.ledger)
    if live is None:
        print("roadmap-check: the postulate ledger is unreadable")
        return 1

    if args.prune:
        removed = prune(path, tiers, live)
        for title, k in removed:
            print(f"  pruned `{k}` from {title} — no longer a live postulate")
        if removed:
            file_pre, tiers, problems = parse(path)

    for lineno, why in problems:
        print(f"SHAPE  {path}:{lineno}  {why}")
        fail = True

    members = group_of(tiers)
    stale = [(g, k) for _t, g, k in members if not any(matches(k, n) for n in live)]
    for g, k in stale:
        print(f"STALE  {path}:{g.lineno}  {g.title} names `{k}`, which is not a live postulate")
        fail = True

    for n in live:
        owners = sorted({g.title for _t, g, k in members if matches(k, n)})
        if not owners:
            print(f"UNCOVERED  `{n}` is a live postulate no group names")
            fail = True
        elif len(owners) > 1:
            print(f"TWICE  `{n}` is a member of {', '.join(owners)}")
            fail = True

    def budget(what, lines, cap, where):
        nonlocal fail
        cost = prose_cost(lines)
        if cost > cap:
            print(f"OVER BUDGET  {path}:{where}  {what}: {cost} chars of prose (cap {cap})")
            fail = True

    budget("the file's preamble", file_pre, FILE_BUDGET, 1)
    for t in tiers:
        budget(f"tier {t.name}'s description", t.pre, TIER_BUDGET, t.lineno)
        for g in t.groups:
            budget(f"group {g.title}", g.prose, GROUP_BUDGET, g.lineno)

    dates = [(path, d) for d in dated_lines(path)]
    extra = ([pathlib.Path(p) for p in args.dates_only] if args.dates_only is not None
             else [ROOT / f for f in DATE_ONLY_FILES]
             + sorted(p for g in DATE_ONLY_GLOBS for p in ROOT.glob(g)))
    dates += [(p, d) for p in extra if p.exists() for d in dated_lines(p)]
    for p, (lineno, d) in dates:
        print(f"DATED  {p}:{lineno}  {d}")
        fail = True

    if fail:
        print("\nroadmap-check: FAIL — the rules are CLAUDE.md's PROOF-STATE section;"
              " mechanics in docs/roadmap-check.md")
        return 1
    ngroups = sum(len(t.groups) for t in tiers)
    print(f"roadmap-check: {len(live)} live postulate(s) in {ngroups} group(s), each in"
          " exactly one; within budget; no dates")
    return 0


if __name__ == "__main__":
    sys.exit(main())
