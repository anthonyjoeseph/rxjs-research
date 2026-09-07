#!/usr/bin/env python3
"""SETTLE RISK NEAR THE TRUNK: while a tier holds an open FALSITY or SHAPE
row, a commit may not DISCHARGE a GRINDABLE or DIFFICULTY row of that tier.

WHAT THIS DEFENDS, and it is a scheduling failure rather than a proof one.
De-risk mode orders work by risk reduced per unit effort, and the roadmap's
own rule already says so in prose: work the tier's top leg, and do not fan
out across its mechanical rows while something above them is open.  The pull
the other way is structural.  `roadmap-moved` requires every commit to move
the roadmap; a risky leg routinely ends in a FINDING rather than a discharge;
and a finding-only commit reads as unfinished, because the ledger it leaves
behind has the same rows in the same classes.  So a mechanical row gets
closed alongside it to make the commit feel whole -- and a GRINDABLE row
proven under an open FALSITY is proven on ground that may still move.  Every
hour spent there is forfeit if the statement above it is refuted, which is
what makes the ordering worth a check rather than a preference.

WHY A PROHIBITION AND NOT AN OBLIGATION.  The tempting shape is a
disjunction: a commit must write evidence OR discharge something risky.  It
does not work, and the reason is worth keeping because it is not obvious.
The commit this exists to stop ALREADY writes evidence -- the finding is the
evidence -- so the disjunction is satisfied by exactly the commit it was
drawn against, and the mechanical row rides along untouched.  It would also
fire on almost nothing, since nearly every commit here moves a row or touches
a header, and a check that never fires teaches nobody anything.  The negative
form has neither problem: it names the move that is forbidden.

WHAT COUNTS AS A DISCHARGE, and this is the whole precision of the check.  A
row may be DELETED, RENAMED, SPLIT, RESTATED or RECLASSIFIED at any time --
the proof must be free to take the shape it needs, and every one of those is
the shape changing rather than a claim being banked.  A DISCHARGE is the one
move that banks: the name stops being a live postulate and is STILL DECLARED
in agda/src, i.e. the postulate became a proven definition.  That is the same
split `check-roadmap.py` draws between a discharged row and a vanished one,
read here for a different purpose.  A name that left agda/src entirely is a
deletion and is free; a name still on the postulate ledger under a different
class is a reclassification and is free.

THE CARVE-OUT IS THE PREREQUISITE ONE, AND IT IS VALIDATED RATHER THAN
ASSERTED.  A mechanical row the risky row actually CONSUMES is fair game --
grinding it is working the top leg, not avoiding it.  But "adjacent", "same
family" and "same module" are not that, and the near miss is the common case,
since a candidate unblocking a SIBLING of the risky row reads exactly like
one unblocking the risky row.  So the risky postulate's own header or
statement must NAME the discharged one, which is the same standard `TWIN:`
is held to: a precedent that is only claimed is not a precedent.
"""
import argparse
import importlib.util
import os
import pathlib
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

RISKY = ("FALSITY", "SHAPE")
MECHANICAL = ("GRINDABLE", "DIFFICULTY")


def _load(name):
    """Import a sibling script, so the tools cannot drift apart."""
    path = os.path.join(REPO, "scripts", name + ".py")
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


class Text:
    """A path-alike over an in-memory roadmap, so the parser can read a git
    blob without either side learning about the other.  `parse` asks for
    exactly one thing and this supplies exactly that."""

    def __init__(self, text):
        self._text = text

    def read_text(self, *a, **k):
        return self._text


def claimed_names(tiers, classes):
    """-> {tier: [name]} for CLAIM-headed rows in the given classes.

    A descriptive head ("`X`'s residue") names a PARENT rather than claiming
    it, so it is not a row anything can be said to have discharged; only a
    head that is nothing but names and separators claims them.
    """
    rm = _CR
    out = {}
    for tier, rows, _pre, _legs, _qs in tiers:
        for label, cls, _lineno, _cost in rows:
            if cls not in classes or not rm.is_claim_head(label):
                continue
            for group in rm.head_groups(label):
                out.setdefault(tier, []).append(group)
    return out


def discharged(groups, live, srcnames):
    """The names in `groups` that became PROVEN DEFINITIONS: no member is a
    live postulate any more, and a member is still declared in agda/src.

    A group is a set of ALTERNATIVE readings of one head token, so it is
    discharged only when no reading of it is still open."""
    out = []
    for group in groups:
        if any(any(_CR.covered(l, {g}) for l in live) for g in group):
            continue
        still = [g for g in group if g in srcnames]
        if still:
            out.append(still[0])
    return out


def still_open(groups, live):
    """The groups with at least one member still on the postulate ledger."""
    return [g for g in groups
            if any(any(_CR.covered(l, {m}) for l in live) for m in g)]


DECL_OF_RE = "^[ \t]*{}[ \t]*:(?:[ \t]|$)"


def header_text(root, name):
    """The comment block directly above `name`'s declaration, plus the
    declaration's own type.  This is what CLAUDE.md means by "the risky row's
    own statement or header must name the candidate": a prerequisite that is
    genuinely consumed is visible in one of the two, and one that is neither
    stated nor written down is the near miss the carve-out must not admit."""
    pat = re.compile(DECL_OF_RE.format(re.escape(name)))
    chunks = []
    for f in sorted((root / "agda" / "src").rglob("*.agda")):
        lines = f.read_text().splitlines()
        for i, line in enumerate(lines):
            if not pat.match(line):
                continue
            j = i - 1
            while j >= 0 and lines[j].lstrip().startswith("--"):
                j -= 1
            k = i + 1
            while k < len(lines) and (lines[k].startswith((" ", "\t"))
                                      or not lines[k].strip()):
                k += 1
            chunks.append("\n".join(lines[j + 1:k]))
    return "\n".join(chunks)


def load_headers(fixture):
    """Fixture form of `header_text`: blocks introduced by `=== <name>`."""
    out, cur = {}, None
    for line in pathlib.Path(fixture).read_text().splitlines():
        if line.startswith("=== "):
            cur = line[4:].strip()
            out[cur] = []
        elif cur is not None:
            out[cur].append(line)
    return {k: "\n".join(v) for k, v in out.items()}


COMMENT_RE = re.compile(r"^[ \t]*--")
TOKEN_RE = re.compile(r"[^\s(){};:,]+")


def names_in(text):
    """The names a chunk genuinely REFERS to, read differently on each side of
    it because the two sides name things differently.

    In the COMMENT half only a backticked token counts, which is this repo's
    own rule for a reference and exists because English is full of words this
    tree happens to declare -- a bare word resolves by accident, and an
    accident is precisely what must not buy the carve-out.  In the STATEMENT
    half a bare token is the real thing: Agda has no backticks, and a name in
    a type is a dependency the typechecker enforces.
    """
    names = set()
    for line in text.splitlines():
        if COMMENT_RE.match(line):
            names |= set(re.findall(r"`([^`]+)`", line))
        else:
            names |= set(TOKEN_RE.findall(line))
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", default="PROOF-STATE.md")
    ap.add_argument("--baseline-file", default=None,
                    help="compare against this file instead of git (selftest)")
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--ledger", default=None,
                    help="live-postulate names (selftest fixture)")
    ap.add_argument("--src-names", default=None,
                    help="agda/src declared names (selftest fixture)")
    ap.add_argument("--headers", default=None,
                    help="risky postulates' headers (selftest fixture)")
    args = ap.parse_args()

    try:
        cur_text, base_text, against, _ef, _et = _CRM.resolve_endpoints(
            args.file, args.ref, args.baseline_file)
    except _CRM.Unreadable as e:
        print(f"roadmap-order: {e}")
        return 1
    except _CRM.NoBaseline as e:
        print(f"roadmap-order: {e}, passing")
        return 0

    root = pathlib.Path(REPO)
    live = _CR.live_postulates(root, args.ledger)
    if live is None:
        print("roadmap-order: cannot read the postulate ledger — passing")
        return 0
    if args.src_names:
        srcnames = set(pathlib.Path(args.src_names).read_text().split())
    else:
        srcnames = _CR.src_decl_names(root)

    was = claimed_names(_CR.parse(Text(base_text)), MECHANICAL)
    now = claimed_names(_CR.parse(Text(cur_text)), RISKY)
    headers = load_headers(args.headers) if args.headers else None

    findings = []
    for tier, groups in sorted(was.items()):
        banked = discharged(groups, live, srcnames)
        if not banked:
            continue
        blockers = still_open(now.get(tier, []), live)
        if not blockers:
            continue
        for name in banked:
            excused = None
            for grp in blockers:
                for risky in grp:
                    text = (headers.get(risky, "") if headers is not None
                            else header_text(root, risky))
                    if name in names_in(text):
                        excused = risky
                        break
                if excused:
                    break
            if not excused:
                findings.append((tier, name, [g[0] for g in blockers]))

    if not findings:
        print(f"roadmap-order: OK — no mechanical row was banked under an open "
              f"FALSITY or SHAPE row (against {against})")
        return 0

    print(f"roadmap-order: FAIL — {len(findings)} row(s) discharged while their "
          f"tier's riskiest rows are still open (against {against}):")
    for tier, name, blockers in findings:
        shown = ", ".join(f"`{b}`" for b in blockers[:3])
        more = f", +{len(blockers) - 3} more" if len(blockers) > 3 else ""
        print(f"\n  Tier {tier}: `{name}` was GRINDABLE/DIFFICULTY and is now a "
              f"proven definition,")
        print(f"    but Tier {tier} still holds open FALSITY/SHAPE: {shown}{more}")
    print("\nSETTLE RISK NEAR THE TRUNK.  A mechanical row proven under an open")
    print("FALSITY is proven on ground that may still move: if the statement above")
    print("it is refuted, the work is not delayed, it is FORFEIT.  Work the tier's")
    print("top leg instead.")
    print("\nThe proof may still take whatever shape it needs — DELETING, RENAMING,")
    print("SPLITTING, RESTATING and RECLASSIFYING these rows are all free.  Only")
    print("BANKING one is held, and only while something riskier is open.")
    print("\nIf the row really is a PREREQUISITE the risky row consumes, say so where")
    print("it can be checked: name it in the risky postulate's own header or")
    print("statement, exactly as a `TWIN:` names its precedent.")
    return 1


_CR = _load("check-roadmap")
_CRM = _load("check-roadmap-moved")

if __name__ == "__main__":
    sys.exit(main())
