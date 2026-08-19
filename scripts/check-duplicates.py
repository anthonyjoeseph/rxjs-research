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
types are equal up to renaming of bound variables.

IT DOES NOT ASSUME AGDA CATCHES THE SAME-NAME CASE.  This file argued
for a while that ClashingDefinition covers two copies sharing a name, so
only differing names needed checking.  That is FALSE whenever either
copy is `private`, or the two modules are simply never in scope
together — and both escapees were exactly that (`dbl-suc` and
`2*suc≤2^suc`, verbatim in .Subscribe-Face and .Caps-Face/Part6).  So a
finding is two SITES, not two names; see `collisions`.

TWO TIERS, because "the same fact" is coarser than "the same type".
A STRICT match is textual equality of the type up to renaming of bound
variables.  A LOOSE match additionally erases the binder TELESCOPE's
brackets and annotations, so that these three spellings of one fact
collide as they should:

    dbl      : ∀ X → 2 * X ≡ X + X            -- binder inferred
    2X≡X+X   : ∀ (X : ℕ) → 2 * X ≡ X + X      -- binder annotated
    ≤ᵇ-true  : ∀ (a b : ℕ) → a ≤ b → …        -- explicit
    ≤→≤ᵇ     : ∀ {m n : ℕ} → m ≤ n → …        -- implicit

Explicit and implicit ARE different types, and merging them costs an
eta-expansion at the call sites — but they are not different FACTS, and
this check is about facts.  Both tiers fail the gate; the loose tier
exists as a separate bucket only so the report can say which kind of
collision it found, since the two need different repairs.

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

BINDER = re.compile(r"[{(]\s*([^:{}()]+?)\s*:")
# `∀ X →` / `∀ x y →` bind names with NO type annotation, so the BINDER
# pattern above (which needs a `:`) never sees them.
#
# ⚠ THE CHARACTER CLASS HERE IS THE WHOLE DIFFICULTY, and getting it
# wrong is SILENT.  This read `[A-Za-zÀ-￿][^\s{}():]*` until 2026-08-19,
# and `À-￿` is U+00C0–U+FFFF — which contains `→` (U+2192), `≡`, `∧`,
# `≤` and every other operator in this development.  So on any type with
# a bare `∀` it consumed the operators as binder NAMES and `alpha` then
# renamed them into slots: `∀ a b → a ∧ b ≡ true → …` and
# `∀ a b → a ∨ b ≡ false → …` normalised to the SAME key.  A duplicate
# checker that reports two unrelated lemmas as one fact is worse than
# none, so match by DELIMITER instead of by character class: a bare
# telescope runs from `∀` to the first `→`, and any bracket or colon in
# between means it was an annotated binder that BINDER already handles.
BARE = re.compile(r"∀\s+([^→(){}:]+?)\s*→")
# An annotated binder group, innermost-first so nesting unwinds by
# iteration: `(p : A → Bool)` ↦ `p`, `{Γ : Ctx n}` ↦ `Γ`.
ANNOT = re.compile(r"[({]\s*([^:{}()]+?)\s*:\s*[^{}()]*?\s*[)}]")
# An ATOMIC type synonym — `Id = ℕ`, `RegId = ℕ`.  Expanding these is
# sound (it is a definitional equality) and it closes a third way one
# fact wears two types: `(id : Id)` against `(id : ℕ)`.  Deliberately
# atomic-only: the multi-line face aliases (`WalkLevel`, `SiCFace`) name
# whole statements rather than binder types, and expanding those would
# make every key unreadable for no gain.
SYNONYM = re.compile(r"^([A-Za-z][^\s]*)\s*:\s*Set\s*$")


def declarations(path):
    """(name, line, type_text) for every declaration NOT inside a where.

    A `where` opens a scope whose bindings are local to one proof; those
    routinely share a type with each other and with nothing meaningful.
    We track the indent of the innermost open `where` and skip anything
    nested under it."""
    src = io.open(path, encoding="utf-8").read().split("\n")
    out, where_indent, field_indent, i = [], None, None, 0
    while i < len(src):
        line, stripped = src[i], src[i].strip()
        if not stripped or stripped.startswith("--"):
            i += 1
            continue
        indent = len(line) - len(line.lstrip())
        # A `field` block holds RECORD FIELDS, which are not standalone
        # facts and legitimately repeat across records — `Inv` and
        # `BurstInv` both carry `reg-typed` and `horizon-low` by design.
        # It needs its own tracking rather than riding on the enclosing
        # `record … where`, because a MULTI-LINE record header puts
        # `where` at the indent of its last continuation line (11, for
        # `Inv` in .Verify-Well-Formed/Part2) while `field` sits at 2 —
        # so the where-block closed at `field` and spilled every field
        # into the scan as a top-level declaration.
        if field_indent is not None and indent <= field_indent:
            field_indent = None
        if stripped == "field":
            field_indent = indent
            i += 1
            continue
        if field_indent is not None:
            i += 1
            continue
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


def synonyms(paths):
    """Atomic `X : Set` / `X = <one identifier>` pairs, tree-wide."""
    out = {}
    for path in paths:
        src = io.open(path, encoding="utf-8").read().split("\n")
        for i, line in enumerate(src[:-1]):
            # Both lines carry trailing `--` comments in practice
            # (`Id : Set   -- an INSTANT …`), and not stripping them
            # here silently found only 1 of the 2 synonyms in the tree.
            m = SYNONYM.match(line.split("--")[0].strip())
            if not m:
                continue
            rhs = src[i + 1].split("--")[0].strip()
            if rhs.startswith(m.group(1) + " ") or rhs.startswith(m.group(1) + "="):
                rhs = rhs.split("=", 1)[1].strip() if "=" in rhs else ""
                if rhs and re.match(r"^[^\s]+$", rhs):
                    out[m.group(1)] = rhs
    return out


def expand(ty, syns):
    """Replace atomic synonyms by their definitions, as whole tokens."""
    for src, dst in syns.items():
        ty = re.sub(r"(?<![^\s{}()\[\]→,])" + re.escape(src)
                    + r"(?![^\s{}()\[\]→,])", dst, ty)
    return ty


def loose(ty):
    """`alpha` with the binder telescope's brackets and annotations
    erased, so explicit/implicit/inferred spellings of one fact agree."""
    for _ in range(40):
        nxt = ANNOT.sub(r"\1", ty)
        if nxt == ty:
            break
        ty = nxt
    return alpha(ty)


def alias_pair(a, b):
    """The mandated private-impl + abstract-alias idiom."""
    return a == b + "-go" or b == a + "-go"


def collisions(buckets):
    """Buckets proving one fact at two or more SITES.

    A site is a (name, file) pair, NOT a name.  Keying on names alone
    misses the copy that wears the SAME name in a different module, and
    this docstring used to argue that Agda's ClashingDefinition covers
    that case — it does not, whenever either copy is `private` or the
    two modules are never in scope together.  Both escapees were exactly
    that shape: `dbl-suc` and `2*suc≤2^suc`, verbatim in .Subscribe-Face
    and in .Caps-Face/Part6's private block, invisible to Agda and to
    this check until 2026-08-19.  Same name in ONE file is not a
    finding — that is a with-clause continuation, or a real
    ClashingDefinition Agda will raise itself."""
    out = []
    for ty, ds in buckets.items():
        sites = {(d[0], d[1]) for d in ds}
        names = sorted({d[0] for d in ds})
        if len(sites) < 2:
            continue
        if len(names) == 2 and alias_pair(*names):
            continue
        if frozenset(names) in DELIBERATE:
            continue
        out.append((ty, sorted(ds, key=lambda d: (d[1], d[2]))))
    out.sort(key=lambda f: (-len(f[1]), f[0]))
    return out


def report(title, findings):
    for ty, ds in findings:
        print()
        print("  [%s] %s" % (title, ty.replace("\x00", "·")[:140]))
        for nm, rel, ln in ds:
            print("      %-30s %s:%d" % (nm, rel, ln))


def main():
    gate = "--gate" in sys.argv
    root = SRC
    if "--src" in sys.argv:
        root = sys.argv[sys.argv.index("--src") + 1]
    paths = [os.path.join(dp, f)
             for dp, _, fs in os.walk(root) for f in sorted(fs)
             if f.endswith(".agda")]
    syns = synonyms(paths)

    strict = collections.defaultdict(list)
    loosely = collections.defaultdict(list)
    scanned = 0
    for path in paths:
        for name, line, ty in declarations(path):
            if not RELATION.search(ty) or len(ty) < MIN_TYPE_LEN:
                continue
            scanned += 1
            ty = expand(ty, syns)
            where = (name, os.path.relpath(path, root), line)
            strict[alpha(ty)].append(where)
            loosely[loose(ty)].append(where)

    s_find = collisions(strict)
    seen = {frozenset(d[0] for d in ds) for _, ds in s_find}
    l_find = [(t, ds) for t, ds in collisions(loosely)
              if frozenset(d[0] for d in ds) not in seen]

    print("check-duplicates: %d propositional declarations, %d synonym(s), "
          "%d exact + %d up-to-binder group(s)"
          % (scanned, len(syns), len(s_find), len(l_find)))
    report("exact", s_find)
    report("up-to-binder", l_find)

    if not s_find and not l_find:
        print("check-duplicates: clean — no fact is proven under two names")
        return 0
    if gate:
        print()
        print("check-duplicates: FAIL — each group above proves ONE fact "
              "under several names.")
        print("  Fix by moving the fact DOWN to the lowest module that "
              "reaches it and deleting")
        print("  the copies (CLAUDE.md: 'when a fact is proven N times, "
              "move it DOWN').  An")
        print("  [up-to-binder] group differs only in explicit/implicit/"
              "inferred binders, so the")
        print("  merge costs an eta-expansion at the call sites; it is the "
              "same fact either way.")
        print("  If a pair is deliberate, add it to DELIBERATE in this "
              "script WITH A REASON.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
