#!/usr/bin/env python3
"""THE DUPLICATE LAW: no fact is proven twice under two names.

WHY THIS IS A SCRIPT AND NOT A PARAGRAPH.  CLAUDE.md has carried a
SEARCH FIRST section for a long time, and the repo has still re-derived
proven facts at least four times (`pathB?-mono-B`, the Ψ probe series, a
path-length unit, and `1≤slotSize`/`n≤slotsSize`/`n≤sum-tab` on
2026-08-19).  The last of those is the instructive one: the search WAS
run, and it was run for the right shape — it was just scoped to two
files instead of the tree.  A rule you can satisfy while still failing
is a rule that needs a machine, which is the same reason `make wiring`,
`make unsafe-check` and `make strip-selftest` exist.

WHAT IT COMPARES is the DECLARED TYPE, extracted from source and never
retyped — the same discipline `check-wiring.py`'s `signature_text`
follows, and for the same reason.  Two declarations collide when their
types are equal up to renaming of bound variables.  Agda already catches
the case where the NAMES also match (ClashingDefinition); this catches
the case that has actually cost us time, where they do not.

WHAT IT DELIBERATELY DOES NOT REPORT:
  * where-block locals.  `invʲ`, `hU′`, `regs` are hypothesis names
    inside a proof, not facts anyone could reuse; several dozen share a
    type and none of them is a duplicate.
  * non-propositional declarations.  `ℕ`, `Set`, and the probe programs
    all share a type by construction.
  * the private-impl/abstract-alias pair (`f-go` beside `f`), which
    CLAUDE.md MANDATES on the budget-sufficient spine.  Identical types
    are the point of that idiom, not a defect.
  * anything in DELIBERATE, below, which carries a REASON per entry.

The residue is small and every member of it is a real finding.
"""
import io, os, re, sys, collections

SRC = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                   "agda", "src")

# Pairs kept apart on purpose.  A frozenset of the two names -> why.
# ADDING AN ENTRY IS A RULING, so it carries a reason and a date; an
# entry without one is indistinguishable from an unexamined failure.
DELIBERATE = {}

KEYWORDS = {"module", "open", "import", "postulate", "mutual", "opaque",
            "private", "abstract", "where", "data", "record", "field",
            "syntax", "infixl", "infixr", "infix", "variable", "instance",
            "let", "in", "with", "rewrite", "constructor", "public",
            "using", "hiding", "renaming", "primitive"}

DECL = re.compile(r"^(\s*)([^\s(){}@;.\"]+)\s*:(?!=)(.*)$")
# a type with propositional content: some relation, or an explicit ⊥
RELATION = re.compile(r"[≡≤<≥>≢]|→\s*⊥")
# Below this the type carries too little to identify a fact; 14 was
# measured (20 hid `b≤2+2b`/`V≤C`, and 10 finds nothing 14 does not).
MIN_TYPE_LEN = 14

# ⚠ KNOWN BLIND SPOT: an ANNOTATED binder and a BARE one are different
# text, and no renaming closes that gap — `∀ X → 2 * X ≡ X + X` (`dbl`,
# .Measures) and `∀ (X : ℕ) → 2 * X ≡ X + X` (`2X≡X+X`, .Caps) are one
# fact this check reports as two.  They are genuinely siblings here so
# neither can import the other, but do not read a clean run as proof
# that no duplicate of that shape exists.
BINDER = re.compile(r"[{(]\s*([^:{}()]+?)\s*:")
# `∀ X →` / `∀ x y →` bind names with NO type annotation, so the BINDER
# pattern above (which needs a `:`) never sees them and two spellings of
# one statement compare unequal.  Missed `dbl : ∀ X → 2 * X ≡ X + X`
# against `2X≡X+X : ∀ (X : ℕ) → 2 * X ≡ X + X` until 2026-08-19.
BARE = re.compile(r"∀\s+((?:[A-Za-zÀ-￿][^\s{}():]*\s+)*[A-Za-zÀ-￿][^\s{}():]*)\s*→")


def declarations(path):
    """(name, line, type_text) for every declaration NOT inside a where.

    A `where` opens a scope whose bindings are local to one proof; those
    routinely share a type with each other and with nothing meaningful.
    We track the indent of the innermost open `where` and skip anything
    nested under it."""
    src = io.open(path, encoding="utf-8").read().split("\n")
    out, where_indent, i = [], None, 0
    while i < len(src):
        line, stripped = src[i], src[i].strip()
        if not stripped or stripped.startswith("--"):
            i += 1
            continue
        indent = len(line) - len(line.lstrip())
        # A `where` block ends at the next COLUMN-0 line.  It cannot end
        # at "indent <= the where's own indent": Agda's usual layout puts
        # the bindings at exactly the indent of the `where` keyword, so
        # that test fires on the first binding and lets every local
        # through — which is precisely the noise this filter exists to
        # remove.  Column 0 is safe because a `where` is always nested
        # inside a top-level definition, and `postulate`/`mutual`/
        # `opaque` block headers are themselves at column 0.
        if where_indent is not None and (indent == 0 or indent < where_indent):
            where_indent = None
        if re.search(r"(^|\s)where\s*$", line):
            if where_indent is None:
                where_indent = indent
            i += 1
            continue
        if where_indent is not None:
            i += 1
            continue
        m = DECL.match(line)
        if m and m.group(2) not in KEYWORDS:
            name, rest = m.group(2), m.group(3)
            # A type ends at the first NON-BLANK line indented no deeper
            # than the declaration.  Blank lines and interleaved comments
            # must NOT end it: Agda's layout allows both inside a long
            # signature, and stopping there truncates the type — which
            # silently makes unrelated declarations that happen to share
            # an opening hypothesis compare EQUAL.  (Six Caps-Face/Part7
            # faces reported as one duplicate group until this was fixed.)
            body, j = [rest.strip()], i + 1
            while j < len(src):
                cur = src[j]
                if not cur.strip():
                    j += 1
                    continue
                if len(cur) - len(cur.lstrip()) <= indent:
                    break
                if not cur.strip().startswith("--"):
                    body.append(cur.strip())
                j += 1
            ty = " ".join(x for x in body if x).strip()
            if ty:
                out.append((name, i + 1, ty))
            i = j
            continue
        i += 1
    return out


def alpha(ty):
    """Canonicalise bound-variable names in order of first appearance, so
    `∀ {m} (f : Fin m → ℕ) …` and `∀ {n} (f : Fin n → ℕ) …` agree."""
    names = []
    for group in BARE.findall(ty) + BINDER.findall(ty):
        for nm in group.split():
            if nm not in names and re.match(r"^[A-Za-zÀ-￿][^\s]*$", nm):
                names.append(nm)
    out = ty
    for k, nm in enumerate(names):
        out = re.sub(r"(?<![^\s{}()\[\]→,])" + re.escape(nm)
                     + r"(?![^\s{}()\[\]→,])", "\x00%d\x00" % k, out)
    return re.sub(r"\s+", " ", out).strip()


def alias_pair(a, b):
    """The mandated private-impl + abstract-alias idiom."""
    return a == b + "-go" or b == a + "-go"


def main():
    gate = "--gate" in sys.argv
    buckets = collections.defaultdict(list)
    scanned = 0
    for dirpath, _, files in os.walk(SRC):
        for f in sorted(files):
            if not f.endswith(".agda"):
                continue
            path = os.path.join(dirpath, f)
            for name, line, ty in declarations(path):
                if not RELATION.search(ty) or len(ty) < MIN_TYPE_LEN:
                    continue
                scanned += 1
                buckets[alpha(ty)].append(
                    (name, os.path.relpath(path, SRC), line))

    findings = []
    for ty, ds in buckets.items():
        names = sorted({d[0] for d in ds})
        if len(names) < 2:
            continue
        if len(names) == 2 and alias_pair(*names):
            continue
        if frozenset(names) in DELIBERATE:
            continue
        findings.append((ty, sorted(ds, key=lambda d: (d[1], d[2]))))

    findings.sort(key=lambda f: (-len(f[1]), f[0]))
    print("check-duplicates: %d propositional declarations, "
          "%d duplicate-type group(s)" % (scanned, len(findings)))
    for ty, ds in findings:
        print()
        print("  %s" % (ty.replace("\x00", "·")[:150]))
        for nm, rel, ln in ds:
            print("      %-30s %s:%d" % (nm, rel, ln))

    if not findings:
        print("check-duplicates: clean — no fact is proven under two names")
        return 0
    if gate:
        print()
        print("check-duplicates: FAIL — each group above proves ONE fact "
              "under several names.")
        print("  Fix by moving the fact DOWN to the lowest module that "
              "reaches it and deleting")
        print("  the copies (CLAUDE.md: 'when a fact is proven N times, "
              "move it DOWN').  If a")
        print("  pair is deliberate, add it to DELIBERATE in this script "
              "WITH A REASON.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
