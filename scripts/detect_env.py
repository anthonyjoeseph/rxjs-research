#!/usr/bin/env python3
"""Which of the three environments this tooling is running in, right now.

Exactly three, per Anthony: a contributor's own laptop, a Claude Code Remote
cloud container (the kind this script itself may be running in), or a GitHub
Actions runner. Every environment-tuned constant in this tree used to assume
the laptop — `AGDA_DEV_BUDGET ?= 45` chief among them, set from a cold scan
of ONE machine and applied everywhere else too. This is the one place that
decides which environment is live, so a tuned constant is a lookup here
rather than a guess re-litigated at every call site.

DETECTION, WORST SIGNAL FIRST -- because the naive signal for "cloud" is
`CLAUDECODE=1`, and it is USELESS for this: the Claude Code CLI sets it the
same way whether it is running interactively on a contributor's own laptop or
inside a spawned remote container, so it cannot tell the two apart. The
signal that actually means "this process is inside a Claude Code Remote
container" is `CLAUDE_CODE_REMOTE=true`, set only by that launcher, checked
here alongside a non-empty `CLAUDE_CODE_CONTAINER_ID` for the same reason a
second signal ever earns its keep -- either alone is enough, and requiring
both would just be a second way to get the answer wrong. CI is unambiguous:
`GITHUB_ACTIONS=true` is documented, universal, and nothing else touching
this repo sets it, so it is checked first and settles the question outright.
Absent both, it is the laptop -- the fallback, not a detected case, which is
the correct default for a signal nobody has set: every contributor's laptop
predates this file.
"""
from __future__ import annotations

import os

LOCAL, CLOUD, CI = "local", "cloud", "ci"
ENVS = (LOCAL, CLOUD, CI)

LABELS = {
    LOCAL: "local machine",
    CLOUD: "cloud container",
    CI: "GitHub Actions",
}


def detect_env() -> str:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        return CI
    if (os.environ.get("CLAUDE_CODE_REMOTE") == "true"
            or os.environ.get("CLAUDE_CODE_CONTAINER_ID")):
        return CLOUD
    return LOCAL


# `make agda-dev`'s per-file budget (seconds).  The laptop's 45 is the
# original, measured from a full 66-module cold scan sitting in the GAP the
# scan showed (docs/agda-dev.md: "the gap is what makes a budget safe, not
# the margin") -- see typecheck-performance-numbers.md for that scan.
#
# The cloud figure is real too, not guessed, but from a much smaller sample:
# four modules dev-checked cold on a 4-core / 15 GB Claude Code Remote
# container spanning the laptop's own range (Main.agda 6.7s->19.7s,
# Verify-Budget-Sufficient/Caps.agda 21.5s->48.9s, Wet/Part2.agda
# 35.0s->42.8s, Subscribe-Face.agda 22.3s->54.3s) -- worst observed 54.3s,
# against a laptop max of 35.0s.  120 sits well clear of that worst sample
# with room for the run-to-run variance those four already show (a 1.2x-2.9x
# spread against the laptop, not a single clean ratio), the same margin-over-
# variance the laptop budget itself demands, just wider because the sample is
# smaller.  Re-scan (typecheck-performance-numbers.md, "## cloud container")
# before moving it, same as the laptop's.
#
# CI has no measurement of its own yet: GitHub-hosted runners are the same
# shape as the cloud container (4 cores, comparable RAM, both non-macOS), and
# `make gate` DOES take the light path in CI when the changed set allows it
# (`gate-light` -> `dev-changed` -> this budget), so it needs a real number
# and not the laptop's.  Sharing the cloud figure is the honest placeholder;
# a CI job records its own `make gate-heavy` timing already (see the Makefile's
# `perf_record.py` call in the `bg` recipe) and the same mechanism will
# accumulate real `agda-dev`/`dev-changed` rows tagged `ci` the first time a
# PR takes the light path, at which point this can be re-derived from that
# evidence instead of borrowed from the cloud container's.
AGDA_DEV_BUDGET = {
    LOCAL: 45,
    CLOUD: 120,
    CI: 120,
}

# `dev-changed --cone-budget`: the TOTAL wall-clock a whole cone sweep may
# spend, as opposed to the per-module ceiling above.  Scaled by the same
# ratio (120/45, rounded) since a cone sweep is many of the same checks back
# to back and nothing about it is cheaper per module than the figure above.
CONE_BUDGET = {
    LOCAL: 300,
    CLOUD: 800,
    CI: 800,
}


def main(argv: list[str]) -> int:
    env = detect_env()
    if len(argv) > 1 and argv[1] == "--budget":
        print(AGDA_DEV_BUDGET[env])
    elif len(argv) > 1 and argv[1] == "--cone-budget":
        print(CONE_BUDGET[env])
    else:
        print(env)
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main(sys.argv))
