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
"""
import argparse
import subprocess
import sys


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

    if args.baseline_file is not None:
        try:
            base = open(args.baseline_file, encoding="utf-8").read()
        except OSError as e:
            print(f"roadmap-moved: cannot read {args.baseline_file}: {e}")
            return 1
    else:
        base = baseline_from_git(args.file, args.ref)
        if base is None:
            print(f"roadmap-moved: no {args.file} at {args.ref} — nothing to "
                  f"compare against, passing")
            return 0

    if norm(cur) == norm(base):
        print(f"roadmap-moved: FAIL — {args.file} is unchanged against "
              f"{args.ref}.")
        print("  A LEG IS ONE COMMIT.  Either the leg landed — retire it, "
              "promote the other")
        print("  two, write a new third — or it did not, in which case rewrite "
              "the FIRST leg")
        print("  as the work that remains.  Neither outcome leaves this file "
              "untouched.")
        return 1

    print(f"roadmap-moved: {args.file} moved against {args.ref}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
