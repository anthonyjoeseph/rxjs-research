#!/usr/bin/env python3
"""THE PORT BOUNDARY (Anthony): the port carries the old adequacy proof to
the state tree, and nothing else.  Every non-private top-level declaration
under the port directory is checked against the old tower, frozen at a
commit:

  P1  OLD NAMES ONLY.  Its name is declared somewhere in the old tower.  A
      name the old tower never had is new work, which is Tier 1's, not the
      port's.
  P2  A POSTULATE STAYS A POSTULATE.  If every old declaration of the name
      is a postulate, the port's is too: the port may not fill a gap the old
      proof left.
  P3  AN UNPORTED BODY IS POINTED AT.  A port postulate whose old name had a
      body carries `-- OLD BODY: <sha> <path>` in the comment block directly
      above it, and the sha resolves, the path exists there, and the name is
      declared there with a body.  Validated wherever it appears.

Helpers are free: a `private` declaration, or anything local to a clause
(`where`), is part of the body it serves.  Constructors and fields go with
their type.  The match is by NAME only — a ported declaration's type may
change with the engine under it.

Textual, like `check-wiring.py`, whose declaration scan this reuses.

Usage:
    scripts/check-port.py --base SHA [--src DIR] [--port DIR] [--old PATH ...]
"""

import argparse
import importlib.util
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("check_wiring", os.path.join(HERE, "check-wiring.py"))
wiring = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(wiring)

OLD_BODY_RE = re.compile(r"^\s*--\s*OLD BODY:\s*(\S+)\s+(\S+)\s*$")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True)


def kinds_by_file(src_dir, files):
    """name -> {(file, kind)} over every declaration, one scan per file so a
    name declared twice keeps both sites (the wiring scan keeps the first)."""
    out = defaultdict(set)
    for f in files:
        defs, _, postulate_names, order = wiring.extract_definitions(src_dir, [f])[:4]
        for n in order:
            if n.startswith("..."):
                continue
            out[n].add((f, "postulate" if n in postulate_names else defs[n].kind))
    return out


def snapshot(base, paths, into):
    """The old tower at `base`, written under `into`, paths relative to the
    Agda root (`agda-impl/`)."""
    ls = git("ls-tree", "-r", "--name-only", base, "--", *paths)
    if ls.returncode != 0:
        sys.exit(f"port-check: cannot read {base}: {ls.stderr.strip()}")
    files = []
    for p in ls.stdout.split():
        if not p.endswith(".agda"):
            continue
        rel = p.split("/", 1)[1]
        dest = os.path.join(into, rel)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w", encoding="utf-8") as fh:
            fh.write(git("show", f"{base}:{p}").stdout)
        files.append(rel)
    return files


def indent(line):
    return len(line) - len(line.lstrip(" "))


def is_private(lines, i):
    """Whether line `i` sits, at any depth, under a bare `private`."""
    want = indent(lines[i])
    for j in range(i - 1, -1, -1):
        s = lines[j].strip()
        if not s or s.startswith("--"):
            continue
        if indent(lines[j]) < want:
            if s == "private":
                return True
            want = indent(lines[j])
            if want == 0:
                return False
    return False


def header(lines, i):
    """The comment block directly above line `i`, nearest first."""
    out = []
    for j in range(i - 1, -1, -1):
        s = lines[j].strip()
        if not s.startswith("--"):
            break
        out.append(lines[j])
    return out


def check_old_body(sha, path, name):
    """None when `path` at `sha` declares `name` with a body; else why not."""
    if git("cat-file", "-e", f"{sha}^{{commit}}").returncode != 0:
        return f"`{sha}` is not a commit"
    show = git("show", f"{sha}:{path}")
    if show.returncode != 0:
        return f"`{path}` does not exist at `{sha}`"
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "F.agda"), "w", encoding="utf-8") as fh:
            fh.write(show.stdout)
        kinds = {k for _, k in kinds_by_file(d, ["F.agda"]).get(name, set())}
    if not kinds:
        return f"`{path}` at `{sha}` declares no `{name}`"
    if kinds == {"postulate"}:
        return f"`{path}` at `{sha}` declares `{name}` only as a postulate"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True, help="the commit the old tower is frozen at")
    ap.add_argument("--src", default="agda-impl")
    ap.add_argument("--port", default="port", help="the port directory, under --src")
    ap.add_argument("--old", nargs="+", default=["agda-impl/adequacy", "agda-impl/operation/Machine.agda"],
                    help="the old tower's paths, from the repo root")
    a = ap.parse_args()

    with tempfile.TemporaryDirectory() as d:
        old = kinds_by_file(d, snapshot(a.base, a.old, d))

    port_dir = os.path.join(a.src, a.port)
    files = sorted(os.path.relpath(os.path.join(r, f), a.src)
                   for r, _, fs in os.walk(port_dir) for f in fs if f.endswith(".agda"))
    problems = []
    checked = 0
    for f in files:
        with open(os.path.join(a.src, f), encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        defs, _, postulate_names, order = wiring.extract_definitions(a.src, [f])[:4]
        for n in order:
            if n.startswith("..."):
                continue
            i = defs[n].line - 1
            if is_private(lines, i):
                continue
            checked += 1
            where = f"{f}:{n}"
            olds = {k for _, k in old.get(n, set())}
            if not olds:
                problems.append(f"NEW NAME    {where} — the old tower declares no `{n}`")
                continue
            new_postulate = n in postulate_names
            if olds == {"postulate"} and not new_postulate:
                problems.append(f"FILLED GAP  {where} — every old `{n}` is a postulate; the port's must be too")
            refs = [m.groups() for m in map(OLD_BODY_RE.match, header(lines, i)) if m]
            for sha, path in refs:
                why = check_old_body(sha, path, n)
                if why:
                    problems.append(f"BAD OLD BODY {where} — {why}")
            if new_postulate and olds != {"postulate"} and not refs:
                problems.append(f"NO OLD BODY {where} — the old `{n}` had a body; "
                                f"say where with `-- OLD BODY: <sha> <path>` above it")

    for p in problems:
        print(p)
    if problems:
        print(f"port-check: FAIL — {len(problems)} problem(s) over {checked} declaration(s); rules in docs/port-check.md")
        sys.exit(1)
    print(f"port-check: clean ({checked} declaration(s) under {port_dir}, all old names, no gap filled)")


if __name__ == "__main__":
    main()
