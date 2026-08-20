# Worker mechanics

The POLICY — when to delegate, who owns the gate, what a worker may not do — is in
CLAUDE.md. This is the how.

## Pinning the model

Workers run on **Sonnet 4.6**, and `model: "sonnet"` does NOT get you there: the Agent
tool's `model` parameter is a hard enum (`sonnet | opus | haiku | fable`) and `sonnet`
resolves to **Sonnet 5** on this provider. Full model IDs are rejected outright with an
InputValidationError.

Two levers actually pin a version, and **both apply only at session start**:

- `export CLAUDE_CODE_SUBAGENT_MODEL=claude-sonnet-4-6` — highest precedence, overrides
  whatever the Agent call passes. **This is the one to use.**
- `.claude/agents/worker-s46.md` carries `model: claude-sonnet-4-6` in its frontmatter
  plus the standing worker rules. Spawn with `subagent_type: "worker-s46"`. A definition
  created mid-session does NOT register — the registry loads at startup.

So **a running session cannot change or verify its workers' model.** If Anthony asks for
4.6, say plainly that it needs one of the two above and cannot be done from inside the
session. If worker output quality visibly degrades — wrong goal types reported, weakened
statements, silent postulate reintroduction — say so and re-assess rather than absorbing
the cost quietly.

## The gate measures the TREE, not the worker

Parallel workers share ONE working directory, so `make wiring-gate` reports on everyone's
uncommitted edits at once. A worker running it while another has `src/` edits in flight
gets a verdict about work that is not its own — observed as a spurious FAIL (eleven
unreachable names that were really a concurrent mid-edit) and as a spurious PASS (a file
edited AFTER the gate was run).

Consequences:

- **A worker's gate result is only meaningful for the files it committed.**
- The design session owns the authoritative post-merge gate.
- **A worker must re-run the gate as its LAST act before committing**, never before its
  final edit.
- A red gate whose cause is another worker's tree is not a licence to commit — it is a
  signal to identify the cause explicitly, confirm your own staged files are clean, and
  say so.

## Commit protocol

**Workers commit and push per green task** to the working branch, in the repo's commit
voice. `make agda && make bug-cache` green before any commit that touches `agda/src`.

**Never reach into another worker's lane to tidy a shared file.** `PROOF-STATE.md` is a
shared ledger, and "helpfully" removing a line for a file another worker is mid-landing
silently retires a row that is still live. Workers report the ledger lines they need; the
design session applies them.

## Reviving a wedged worker

A harness restart kills a worker's in-flight turn. Diagnose via transcript mtime + `ps`;
revive via SendMessage with re-verify instructions. **"queued" = alive, "resumed from
transcript" = was dead.**
