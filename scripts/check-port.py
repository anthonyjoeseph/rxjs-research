#!/usr/bin/env python3
"""THE PORT BOUNDARY (Anthony): the port carries the old adequacy proof to
the pointer-free engine, and proves nothing else.  Checked against the old tower,
frozen at a commit:

  P1  A DEFINITION HAS AN OLD NAME.  A body under a name the old tower never
      had is new proof, which is Tier 1's, not the port's.
  P2  A POSTULATE STAYS A POSTULATE.  If every old declaration of the name
      is a postulate, the port's is too: the port may not fill a gap the old
      proof left.  A NEW postulate is free: stating a gap proves nothing.
  P3  AN UNPORTED BODY IS POINTED AT.  A port postulate whose old name was
      never a postulate carries `-- OLD BODY: <sha> <path>` in the comment block directly
      above it, and the sha resolves, the path exists there, and the name is
      declared there with a body.  Validated wherever it appears.

THE SCOPE is the port directory and its IMPORT CONE, the old tower aside,
so a body cannot leave the boundary by moving to a module the port imports.
In a module that existed at the frozen commit, under the port directory or
in its cone, only what it has gained since is checked: the engine the port
runs on is not the port.  A port directory that IS part of the old tower is
ported in place, so every declaration in it is checked.

A name ending in `ᵀ` is its table reading, and answers to the old name
without the suffix as well as to its own.

Helpers are free: a `private` declaration, or anything local to a clause
(`where`), is part of the body it serves.  Constructors and fields go with
their type.  The match is by NAME only — a ported declaration's type may
change with the engine under it.

Textual, like `check-wiring.py`, whose declaration scan this reuses.

Usage:
    scripts/check-port.py --base SHA [--src DIR] [--port DIR ...] [--old PATH ...]
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


IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([^\s;()]+)")


def cone(src_dir, roots, skip):
    """Every module of `src_dir` the roots reach by import, roots included,
    not following into `skip`."""
    seen, todo = set(), list(roots)
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        with open(os.path.join(src_dir, f), encoding="utf-8") as fh:
            for line in fh:
                m = IMPORT_RE.match(line)
                if not m:
                    continue
                g = m.group(1).replace(".", "/") + ".agda"
                if os.path.exists(os.path.join(src_dir, g)) and not skip(g):
                    todo.append(g)
    return sorted(seen)


def names_at(base, path):
    """Every name `path` declared at `base`; None when it did not exist."""
    show = git("show", f"{base}:{path}")
    if show.returncode != 0:
        return None
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "F.agda"), "w", encoding="utf-8") as fh:
            fh.write(show.stdout)
        return set(kinds_by_file(d, ["F.agda"]))


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
    ap.add_argument("--port", nargs="+", default=["port"], help="the port directories, under --src")
    ap.add_argument("--old", nargs="+", default=["agda-impl/adequacy", "agda-impl/operation/AbstractObservable.agda",
                             "agda-impl/operation/PureObservable.agda", "agda-impl/operation/Observable.agda"],
                    help="the old tower's paths, from the repo root")
    ap.add_argument("--renamed", nargs="*", default=[], metavar="NEW=OLD",
                    help="a cone module under --src, and a path from the repo root it was renamed from: "
                         "what OLD declared at --base counts as declared before")
    a = ap.parse_args()
    renamed = {}
    for r in a.renamed:
        new, old_path = r.split("=", 1)
        renamed.setdefault(new, []).append(old_path)

    with tempfile.TemporaryDirectory() as d:
        old = kinds_by_file(d, snapshot(a.base, a.old, d))

    port_dirs = [os.path.join(a.src, p) for p in a.port]
    roots = sorted(os.path.relpath(os.path.join(r, f), a.src)
                   for d in port_dirs for r, _, fs in os.walk(d) for f in fs if f.endswith(".agda"))
    prefix = os.path.relpath(a.src, git("rev-parse", "--show-toplevel").stdout.strip() or ".")
    tower = [p.split("/", 1)[1] for p in a.old]
    in_tower = lambda f: any(f == t or f.startswith(t.rstrip("/") + "/") for t in tower)
    problems = []
    checked = fresh = 0
    for f in cone(a.src, roots, in_tower):
        with open(os.path.join(a.src, f), encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        before = None
        for path in [] if in_tower(f) else [os.path.join(prefix, f)] + renamed.get(f, []):
            names = names_at(a.base, path)
            if names is not None:
                before = (before or set()) | names
        defs, _, postulate_names, order = wiring.extract_definitions(a.src, [f])[:4]
        for n in order:
            if n.startswith("...") or (before is not None and n in before):
                continue
            i = defs[n].line - 1
            if is_private(lines, i):
                continue
            checked += 1
            where = f"{f}:{n}"
            olds = {k for m in {n, n.removesuffix("ᵀ")} for _, k in old.get(m, set())}
            new_postulate = n in postulate_names
            if not olds:
                if new_postulate:
                    fresh += 1
                else:
                    problems.append(f"NEW NAME    {where} — the old tower declares no `{n}`; only a postulate may be new")
                continue
            if olds == {"postulate"} and not new_postulate:
                problems.append(f"FILLED GAP  {where} — every old `{n}` is a postulate; the port's must be too")
            refs = [m.groups() for m in map(OLD_BODY_RE.match, header(lines, i)) if m]
            for sha, path in refs:
                why = check_old_body(sha, path, n)
                if why:
                    problems.append(f"BAD OLD BODY {where} — {why}")
            if new_postulate and "postulate" not in olds and not refs:
                problems.append(f"NO OLD BODY {where} — the old `{n}` had a body; "
                                f"say where with `-- OLD BODY: <sha> <path>` above it")

    for p in problems:
        print(p)
    if problems:
        print(f"port-check: FAIL — {len(problems)} problem(s) over {checked} declaration(s); rules in docs/port-check.md")
        sys.exit(1)
    print(f"port-check: clean ({checked} declaration(s) in {', '.join(port_dirs)} and their cone; "
          f"every body an old name, no gap filled, {fresh} new postulate(s))")


if __name__ == "__main__":
    main()
