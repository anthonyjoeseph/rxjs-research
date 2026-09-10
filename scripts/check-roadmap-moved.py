#!/usr/bin/env python3
"""THE ROADMAP MUST MOVE IN EVERY BRANCH, because A LEG IS ONE PR.

Either the leg LANDED -- retire it, promote the other two, write a new third --
or the session could not finish what it planned, in which case the first leg is
REWRITTEN as the work that remains.  Neither outcome leaves PROOF-STATE.md
untouched, so an unchanged file means a leg was finished without being retired
or abandoned without being restated.

The check is deliberately dumb (did the file change) because what it defends is
not resolvable by a machine: `check-roadmap.py` verifies that a row's NAME still
exists, and nothing can verify that the plan a leg describes is still the plan.

The comparison ignores trailing whitespace and trailing blank lines, so the
cheapest way to satisfy it is to say something.

THE BASELINE IS THE MERGE-BASE WITH main, NOT THE PREVIOUS COMMIT, and that is
the difference between holding a leg and taxing every keystroke inside one. A
branch lands one leg, but it takes as many commits as the work takes: a repaired
reassembly, a missing import, an error the first build found. Held per COMMIT,
each of those owed the roadmap a line it had nothing to say in, so the rule
bought edits made to satisfy it rather than because the plan had moved — which
is the failure mode of a check whose whole subject is whether someone said
something true. Held per BRANCH, a fix-up costs nothing and a branch that lands
proof work having said nothing about the plan still fails, which is the thing
worth catching.

One reading then covers both contexts, so the old whole-tree-clean fallback is
gone from the branch case: the merge-base is not HEAD, so disk-vs-merge-base
asks the same question mid-work (disk carries the pending edit) and at a CI
checkout (disk equals HEAD, still divergent from the base). The fallback
survives only where the merge-base IS HEAD — on main itself, or a branch that
has not diverged — where it degrades to the previous commit so a direct landing
on main is still held rather than silently exempt.

A stale local `origin/main` only widens the range, making the check EASIER to
satisfy. That is the right direction to fail in for a check whose false
positives are the entire complaint.


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


def head_sha():
    p = subprocess.run(["git", "rev-parse", "HEAD"],
                       capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else None


def merge_base(base_ref):
    """The commit this branch diverged from, or None when there isn't one.

    Tries `origin/<name>` before the bare name so a checkout that has the
    remote ref (CI, with fetch-depth 0) uses it, while a local clone with only
    a tracking branch still resolves. None on every git failure — a shallow
    clone, an unrelated history, a repo with no main — and every caller treats
    that as 'fall back to the per-commit reading' rather than as a pass.
    """
    for ref in (f"origin/{base_ref}", base_ref):
        p = subprocess.run(["git", "merge-base", ref, "HEAD"],
                           capture_output=True, text=True)
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    return None


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


class Unreadable(Exception):
    """A file the caller asked for does not exist — a failure, not a pass."""


class NoBaseline(Exception):
    """No comparison point exists at the requested ref — every caller passes."""


def resolve_endpoints(file, ref, baseline_file=None, base_ref="main"):
    """-> (cur, base, against, exempt_from, exempt_to)

    WHICH TWO VERSIONS OF THE ROADMAP A CHECK IS COMPARING, resolved once
    for every check that asks the question.  The two reading contexts and
    the whole-tree-clean fallback are explained in the module docstring.

    It is a function rather than two copies because that fallback is the
    subtle part, and a second check needing the same endpoints would
    otherwise carry its own copy of it.  A drifted copy answers CI's
    question at a local checkout or the reverse -- which is the one wrong
    answer that produces no symptom, since both readings return a pair of
    plausible file versions and neither raises.
    """
    try:
        cur = open(file, encoding="utf-8").read()
    except OSError as e:
        raise Unreadable(f"cannot read {file}: {e}") from e

    # exempt_from/exempt_to are the two endpoints an exemption check diffs
    # for agda/ paths — kept in lockstep with the endpoints the comparison
    # itself ends up using.
    exempt_from, exempt_to = ref, None

    if baseline_file is not None:
        try:
            base = open(baseline_file, encoding="utf-8").read()
        except OSError as e:
            raise Unreadable(f"cannot read {baseline_file}: {e}") from e
        return cur, base, baseline_file, None, None  # fixtures aren't commits

    # THE BRANCH READING, and it is the one that normally applies: compare
    # against where this branch left main. It needs no clean-tree special
    # case because the merge-base is not HEAD, so the same comparison is
    # correct mid-work and at a CI checkout alike. Only at the default ref
    # — an explicit --ref is a deliberate comparison point, not to be
    # second-guessed — and only when the branch has actually diverged.
    if ref == "HEAD":
        mb = merge_base(base_ref)
        if mb is not None and mb != head_sha():
            base = baseline_from_git(file, mb)
            if base is None:
                raise NoBaseline(
                    f"no {file} at the merge-base with {base_ref} — "
                    "nothing to compare against")
            return cur, base, f"the merge-base with {base_ref}", mb, None

    base = baseline_from_git(file, ref)
    if base is None:
        raise NoBaseline(f"no {file} at {ref} — nothing to compare against")
    against = ref

    # NO DIVERGENCE, so the branch reading above has nothing to compare —
    # this is main itself, or a branch level with it. Fall back to the
    # per-commit question so a direct landing on main is still held.
    # This file matches the ref *and* nothing else in the tree is dirty
    # either — a whole-tree-clean checkout, which is what CI always looks
    # like, committed edit included. That makes disk-vs-ref compare HEAD
    # against itself, so re-ask the question CI needs answered instead:
    # did HEAD's own commit move the file, i.e. does HEAD differ from
    # HEAD~1. A dirty tree that merely leaves THIS file untouched (the
    # ordinary local-dev "haven't written the roadmap update yet" case)
    # must not take this branch — the working-tree-clean gate is what
    # keeps the two apart.
    if ref == "HEAD" and norm(cur) == norm(base) and working_tree_clean():
        parent = baseline_from_git(file, "HEAD~1")
        if parent is None:
            raise NoBaseline(f"no {file} at HEAD~1 — nothing to compare against")
        base = parent
        against = "HEAD~1"
        exempt_from, exempt_to = "HEAD~1", "HEAD"

    return cur, base, against, exempt_from, exempt_to


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", default="PROOF-STATE.md")
    ap.add_argument("--baseline-file", default=None,
                    help="compare against this file instead of git (selftest)")
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--base-ref", default="main",
                    help="branch this one is measured against (default main)")
    args = ap.parse_args()

    try:
        cur, base, against, exempt_from, exempt_to = resolve_endpoints(
            args.file, args.ref, args.baseline_file, args.base_ref)
    except Unreadable as e:
        print(f"roadmap-moved: {e}")
        return 1
    except NoBaseline as e:
        print(f"roadmap-moved: {e}, passing")
        return 0

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
        print("  A LEG IS ONE PR.  Either the leg landed — retire it, "
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
