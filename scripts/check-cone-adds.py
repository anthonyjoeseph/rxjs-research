#!/usr/bin/env python3
"""A NEW DECLARATION MAY NOT BE ADDED TO A DEEP MODULE (Anthony).

A module's REVERSE CONE is the set of modules that transitively import it --
what an edit to it INVALIDATES.  Editing near the bottom of the tree is
therefore not merely slower, it is slower by a factor nobody sees while typing:
`Verify-Budget-Sufficient.Measures` has a reverse cone of 72 of 132 modules, so
a four-line lemma placed there costs a rebuild of 55% of the tree to verify
something the dev loop would have checked in seconds one level up -- and where
a module in that cone has itself outgrown the loop, it costs a CI gate instead.

WHAT MAKES THE RULE DECIDABLE IS THAT AN ADDITION IS RELOCATABLE AND AN EDIT IS
NOT.  A change to an existing definition has no choice about where it lands:
the definition lives where it lives, and the cone bill is already owed.  A NEW
declaration has no home yet, so the bill is being paid for nothing -- it could
have gone in a new module importing this one, where it checks in seconds and
invalidates nobody.  So the check fires on exactly one shape: a PURELY ADDITIVE
edit (no line removed) to a module whose reverse cone is at or over the
threshold.  An addition made alongside a modification is free and stays legal.

CALIBRATION, over the 80 commits before this check existed: 227 edits to files
under agda/src, of which TWO were purely-additive edits to a module with a cone
of 50 or more -- one adding a transport to `Measures` (cone 72), one adding a
`Val` recursion to `Rx.Exp` (cone 123, the deepest module in the tree).  Both
are the shape this rule exists to stop.  At a threshold of 30 it fires on 29%
of such edits, which is noise; at 100 it never fires at all, missing `Measures`
and so missing the case that prompted it.  50 is where the signal is.

COMMENTS ARE STRIPPED BEFORE THE DIFF IS READ, and that is load-bearing rather
than tidy: a `-- PROBED` receipt or a `-- DEAD ROUTE` line added to a deep
postulate's header is a purely additive edit to a deep module, and it costs
NOTHING, because `agda/_stripped-comments/` is invariant under it.  A check
that fired there would fire mainly on the evidence conventions this repo
mandates elsewhere, which is how a rule teaches people to route around it.

A FILE THAT DID NOT EXIST AT THE BASELINE IS EXEMPT, because it is not an
addition to a deep module -- it IS the new module the rule asks for.
"""
import argparse
import collections
import importlib.util
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC = "agda/src"
DEFAULT_THRESHOLD = 50

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.'-]+)")


def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, filename))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def module_of(path):
    return os.path.relpath(path, SRC)[:-len(".agda")].replace("/", ".")


def reverse_cones(src_dir):
    """module -> how many modules transitively import it."""
    deps = {}
    for dirpath, _, files in os.walk(src_dir):
        for f in files:
            if not f.endswith(".agda"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, src_dir)[:-len(".agda")].replace("/", ".")
            with open(p, encoding="utf-8", errors="replace") as fh:
                deps[rel] = {m.group(1) for ln in fh if (m := IMPORT.match(ln))}
    own = set(deps)
    rev = collections.defaultdict(set)
    for m, ds in deps.items():
        for d in ds:
            if d in own:
                rev[d].add(m)
    out = {}
    for m in own:
        seen, stack = set(), [m]
        while stack:
            for y in rev.get(stack.pop(), ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        out[m] = len(seen)
    return out


def stripped(text, strip_text):
    """Comment-free text, or None when the stripper declines the file (a block
    comment) -- declining is conservative: the caller then treats the edit as
    not provably additive and lets it through, since a check cannot establish
    the shape of an edit it cannot read."""
    if text is None:
        return None
    body, _, skipped = strip_text(text)
    return None if skipped else body


def purely_additive(before, after):
    """True when `after` is `before` with lines only inserted.

    A subsequence test rather than a diff parse: every line of `before` must
    still appear, in order, in `after`.  That is exactly 'nothing was removed
    or changed', which is the property the rule needs, and it needs no hunk
    parsing and no attribution of lines to declarations -- an attribution the
    first cut of this check DID attempt, and which made it fire on nothing at
    all, because a new lemma's header comment attaches to its PREDECESSOR and
    so made every neighbour read as modified.
    """
    b = [ln for ln in before.split("\n") if ln.strip()]
    a = [ln for ln in after.split("\n") if ln.strip()]
    if len(a) <= len(b):
        return False
    it = iter(a)
    return all(any(x == ln for x in it) for ln in b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD,
                    help="reverse-cone size at which a module is 'deep'")
    ap.add_argument("--base-ref", default="main")
    ap.add_argument("--src", default=SRC)
    ap.add_argument("--root", default=ROOT,
                    help="repository to check (the selftest drives a scratch one)")
    ap.add_argument("--list", action="store_true",
                    help="print every module's reverse cone and exit")
    args = ap.parse_args()

    os.chdir(args.root)           # every git call below runs in this repo
    src_dir = os.path.join(args.root, args.src)
    cones = reverse_cones(src_dir)

    if args.list:
        try:
            for m, c in sorted(cones.items(), key=lambda kv: -kv[1]):
                mark = "  DEEP" if c >= args.threshold else ""
                print(f"{c:5d}  {m}{mark}")
        except BrokenPipeError:      # `| head` is the expected way to read this
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        return 0

    moved = _load("check_roadmap_moved", "check-roadmap-moved.py")
    strip_text = _load("strip_comments_mod", "strip-comments.py").strip_text

    base = moved.merge_base(args.base_ref)
    if base is None or base == moved.head_sha():
        base = "HEAD"
    changed = moved.changed_paths(base)
    if changed is None:
        print("cone-check: cannot read the diff — passing rather than guessing")
        return 0

    findings = []
    for f in changed:
        if not (f.startswith(args.src + "/") and f.endswith(".agda")):
            continue
        before = stripped(moved.baseline_from_git(f, base), strip_text)
        if before is None:
            continue                      # new file, or unreadable — exempt
        try:
            after = stripped(open(os.path.join(args.root, f), encoding="utf-8").read(),
                             strip_text)
        except OSError:
            continue                      # deleted — never an addition
        if after is None or not purely_additive(before, after):
            continue
        mod = module_of(f)
        cone = cones.get(mod, 0)
        if cone >= args.threshold:
            findings.append((f, mod, cone))

    if not findings:
        print(f"cone-check: no purely-additive edit to a module with a reverse "
              f"cone ≥ {args.threshold}")
        return 0

    print("cone-check: FAIL — a NEW declaration was added to a DEEP module.")
    for f, mod, cone in findings:
        print(f"  {f}")
        print(f"    an edit here invalidates {cone} modules, and this edit "
              "removed nothing —")
        print("    so the cone is being paid for a declaration that has no "
              "home yet.")
    print()
    print("  Put it in a NEW module that imports this one: it checks in "
          "seconds, invalidates")
    print("  nobody, and `make find` reaches it either way.  An addition made "
          "ALONGSIDE a")
    print("  modification is free and needs no move — this fires only on a "
          "purely additive")
    print("  edit.  `scripts/check-cone-adds.py --list` ranks every module by "
          "what it costs.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
