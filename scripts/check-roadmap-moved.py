#!/usr/bin/env python3
"""THE ROADMAP MUST MOVE IN EVERY COMMIT, because A LEG IS ONE COMMIT.

Either the leg LANDED -- retire it, promote the other two, write a new third --
or the session could not finish what it planned, in which case the first leg is
REWRITTEN as the work that remains.  Neither outcome leaves PROOF-STATE.md
untouched, so an unchanged file means a leg was finished without being retired
or abandoned without being restated.

The check is deliberately dumb (did the file change against HEAD) because what
it defends is not resolvable by a machine: `check-roadmap.py` verifies that a
row's NAME still exists, and nothing can verify that the plan a leg describes is
still the plan.

The comparison ignores trailing whitespace and trailing blank lines, so the
cheapest way to satisfy it is to say something.

Two contexts read "against HEAD" differently, and the check answers each on its
own terms rather than picking one. Mid-work, the working tree carries the
pending edit and HEAD is the last commit, so comparing disk against `git show
HEAD:path` is already the right question. Once that edit is committed — the
state a CI checkout is always in, disk and HEAD identical by construction — the
same comparison always reads "unchanged" no matter what the commit did, because
it is comparing HEAD against itself. So when disk already matches HEAD, the
check falls back to asking the question CI actually needs answered: did HEAD's
own commit move the file, i.e. does HEAD differ from HEAD~1. The fallback only
fires at the default ref; an explicit --ref keeps the plain disk-vs-ref reading.

An unchanged roadmap is only a finding when there was proof work to report. A
commit touching nothing under agda/ — CI tooling, docs, CLAUDE.md itself — has
no leg to retire or restate, so it is exempt; the exemption is read from the
same two endpoints already used for the movement comparison, never from a
separate rule about "which PR this is". "Touching agda/" means touching what
Agda actually checks: a comment-only edit there (a stale marker deleted, a
`-- PROBED` line added) is already free by this repo's own design — the
`agda/_stripped-comments/` mirror is invariant under it — so the exemption
reuses `strip-comments.py`'s stripper rather than a raw path match, and a
change that survives stripping still owes the roadmap a line.
"""
import argparse
import importlib.util
import os
import subprocess
import sys

_STRIP_MODULE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "strip-comments.py")


def _load_strip_text():
    spec = importlib.util.spec_from_file_location("strip_comments_mod",
                                                    _STRIP_MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.strip_text


def norm(text):
    lines = [ln.rstrip() for ln in text.replace("\r\n", "\n").split("\n")]
    while lines and lines[-1] == "":
        lines.pop()
    return "\n".join(lines)


def baseline_from_git(path, ref):
    p = subprocess.run(["git", "show", f"{ref}:{path}"],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return p.stdout


def changed_paths(ref_from, ref_to=None):
    """Paths differing between ref_from and ref_to (working tree if None).
    None on a git failure — the caller must not treat that as 'nothing
    changed' and skip the check on a shaky answer."""
    cmd = ["git", "diff", "--name-only", ref_from] + ([ref_to] if ref_to else [])
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return [f for f in p.stdout.splitlines() if f]


def working_tree_clean():
    """True only when nothing in the whole tree is dirty against HEAD — the
    signal that this file matching HEAD means a CI checkout, not merely that
    the pending edit happens to leave this one file alone."""
    p = subprocess.run(["git", "status", "--porcelain"],
                       capture_output=True, text=True)
    return p.returncode == 0 and p.stdout.strip() == ""


def content_at(path, ref):
    """File content at ref, or in the working tree when ref is None. None on
    a missing file — added or deleted is never comment-only."""
    if ref is None:
        try:
            return open(path, encoding="utf-8").read()
        except OSError:
            return None
    return baseline_from_git(path, ref)


def agda_content_changed(ref_from, ref_to, strip_text):
    """True if any agda/ path differs from ref_from to ref_to (working tree
    when ref_to is None) once full-line comments are stripped — i.e. there is
    something here Agda actually checks differently. A file Agda would refuse
    to strip (a block comment) or one that was added/removed is conservatively
    treated as changed, since comment-only-ness cannot be established."""
    files = changed_paths(ref_from, ref_to)
    if files is None:
        return True  # can't tell — don't let a shaky git call grant a pass
    for f in files:
        if not f.startswith("agda/"):
            continue
        before, after = content_at(f, ref_from), content_at(f, ref_to)
        if before is None or after is None:
            return True
        before_s, _, before_skip = strip_text(before)
        after_s, _, after_skip = strip_text(after)
        if before_skip or after_skip or before_s != after_s:
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", default="PROOF-STATE.md")
    ap.add_argument("--baseline-file", default=None,
                    help="compare against this file instead of git (selftest)")
    ap.add_argument("--ref", default="HEAD")
    args = ap.parse_args()

    try:
        cur = open(args.file, encoding="utf-8").read()
    except OSError as e:
        print(f"roadmap-moved: cannot read {args.file}: {e}")
        return 1

    # exempt_from/exempt_to are the two endpoints the exemption check diffs
    # for agda/ paths — kept in lockstep with whatever endpoints the movement
    # comparison itself ends up using.
    exempt_from, exempt_to = args.ref, None

    if args.baseline_file is not None:
        try:
            base = open(args.baseline_file, encoding="utf-8").read()
        except OSError as e:
            print(f"roadmap-moved: cannot read {args.baseline_file}: {e}")
            return 1
        against = args.baseline_file
        exempt_from = None  # selftest fixtures aren't git commits
    else:
        base = baseline_from_git(args.file, args.ref)
        if base is None:
            print(f"roadmap-moved: no {args.file} at {args.ref} — nothing to "
                  f"compare against, passing")
            return 0
        against = args.ref

        # This file matches the ref *and* nothing else in the tree is dirty
        # either — a whole-tree-clean checkout, which is what CI always looks
        # like, committed edit included. That makes disk-vs-ref compare HEAD
        # against itself, so re-ask the question CI needs answered instead:
        # did HEAD's own commit move the file, i.e. does HEAD differ from
        # HEAD~1. A dirty tree that merely leaves THIS file untouched (the
        # ordinary local-dev "haven't written the roadmap update yet" case)
        # must not take this branch — the working-tree-clean gate is what
        # keeps the two apart. Only at the default ref — an explicit --ref is
        # a deliberate comparison point and is not second-guessed.
        if args.ref == "HEAD" and norm(cur) == norm(base) and working_tree_clean():
            parent = baseline_from_git(args.file, "HEAD~1")
            if parent is None:
                print(f"roadmap-moved: no {args.file} at HEAD~1 — nothing to "
                      f"compare against, passing")
                return 0
            base = parent
            against = "HEAD~1"
            exempt_from, exempt_to = "HEAD~1", "HEAD"

    if norm(cur) == norm(base):
        if exempt_from is not None:
            strip_text = _load_strip_text()
            if not agda_content_changed(exempt_from, exempt_to, strip_text):
                print(f"roadmap-moved: SKIP — {args.file} unchanged against "
                      f"{against}, but nothing under agda/ changed either "
                      f"(or only comments did) — no leg to report")
                return 0

        print(f"roadmap-moved: FAIL — {args.file} is unchanged against "
              f"{against}.")
        print("  A LEG IS ONE COMMIT.  Either the leg landed — retire it, "
              "promote the other")
        print("  two, write a new third — or it did not, in which case rewrite "
              "the FIRST leg")
        print("  as the work that remains.  Neither outcome leaves this file "
              "untouched.")
        return 1

    print(f"roadmap-moved: {args.file} moved against {against}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
