#!/usr/bin/env python3
"""THE ATTIC: generations deleted wholesale, kept searchable.

The two search commands walk the tree, so a generation removed in one
commit is invisible to both -- and the bigger the removal, the bigger the
blind spot.  That makes the one command the SEARCH FIRST rule tells you to
run answer NO about work that is merely not checked out, which is the worst
possible answer to "has anyone already been here".

`scripts/attic.txt` names the LAST COMMIT STILL HOLDING each such
generation.  This module resolves those shas and materialises their
`agda/src` under `agda/_attic/<sha>/` (gitignored), so `find` and
`find-prose` can walk them exactly as they walk the live tree.

A sha that no longer resolves is a HARD failure rather than a quiet skip,
for the same reason the attic exists at all.
"""
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LIST = os.path.join(HERE, "attic.txt")
CACHE = os.path.join(REPO, "agda", "_attic")
SUBTREE = "agda/src"


def shas():
    """[(sha, label)] per generation named in attic.txt; [] when there is none."""
    if not os.path.exists(LIST):
        return []
    out = []
    with open(LIST, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            sha, _, label = line.partition(" ")
            out.append((sha, label.strip()))
    return out


def materialise(sha):
    """Check the generation out under agda/_attic/<sha>/ once, and return it.

    A cached directory is trusted because a sha names an immutable tree, so
    the second search of a generation costs nothing.
    """
    dest = os.path.join(CACHE, sha)
    if os.path.isdir(dest):
        return dest
    try:
        names = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", sha, "--", SUBTREE],
            cwd=REPO, capture_output=True, text=True, check=True).stdout.split()
    except subprocess.CalledProcessError:
        raise SystemExit(
            "attic: sha %s does not resolve — scripts/attic.txt names a commit\n"
            "       this clone cannot see (a shallow fetch, or a rewritten\n"
            "       history).  Fix the list or deepen the clone; a search that\n"
            "       skipped it would report a false all-clear." % sha)
    if not names:
        raise SystemExit(
            "attic: sha %s resolves but holds no %s — the list names the wrong\n"
            "       commit, and a search of it would report a false all-clear."
            % (sha, SUBTREE))
    tmp = dest + ".part"
    for name in names:
        if not name.endswith(".agda"):
            continue
        blob = subprocess.run(["git", "show", "%s:%s" % (sha, name)],
                              cwd=REPO, capture_output=True, check=True).stdout
        out = os.path.join(tmp, os.path.relpath(name, SUBTREE))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "wb") as fh:
            fh.write(blob)
    # RENAME LAST, so an interrupted materialisation leaves no half-tree that
    # the next run would trust and search -- a partial attic is exactly the
    # false all-clear this whole file exists to prevent.
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    os.replace(tmp, dest)
    return dest


def roots():
    """[(sha, label, dir)] — every generation, materialised and ready to walk."""
    return [(sha, label, materialise(sha)) for sha, label in shas()]
