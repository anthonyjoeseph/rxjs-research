# PROOF-STATE — the canonical design-state index

**Read this first, every session, before any proof work.** Update it in the same
commit as every ruling, every postulate added or discharged, every gap opened or
closed. Detailed records stay in source comments — this file is pointers, not
copies. If a pointer and its source comment disagree, the source comment wins;
fix the pointer.

> **THE WIRING LAW GOVERNS EVERYTHING BELOW — see CLAUDE.md § "The wiring law:
> NEVER LEAVE A PROOF HANGING".** Every gap is a typed postulate; every
> definition and postulate is consumed, transitively, by a top-level theorem.
> `make wiring` is the acceptance test. **The wiring pass is COMPLETE**
> (zero orphans, zero unreachable modules, every postulate consumed) — which is
> what makes the risk accounting below meaningful: the postulate ledger now IS
> the total remaining uncertainty, with nothing hiding outside it.

> **CURRENT OPERATING MODE (Anthony, 2026-08-06): DE-RISK FIRST.** Every
> postulate carries a probability of being FALSE or EMPTY, and the proof's total
> risk is the SUM over the ledger — so the work is ordered by risk reduced per
> unit effort, not by proof-progress optics. Two consequences:
>
> - **A machine refutation of a postulate is as valuable as a proof of one.**
>   Cheaper, usually. A false postulate found NOW costs a restatement; found
>   after the towers above it are ground, it costs the towers.
> - **The truth-audit prohibition from the wiring pass is LIFTED** (it was
>   scoped "during the wiring pass" and the pass is done). Auditing statements
>   for truth — especially by machine probe — is now the priority, not a
>   distraction. The SHORTCUT MANDATE's other half stands: never weaken a
>   statement to make it typecheck, and postulate rather than grind when a gap
>   is real mathematics.

> **PROBE CLEANUP IS ASSEMBLY-FIRST, AND IT IS NOT TIER-GATED (Anthony,
> 2026-08-09).** A probe is TEMPORARY; its end state is **assembly into src plus
> deletion of the probe-side code**. Full-on assembly — postulating whatever
> gaps the assembly needs — is the vastly preferred outcome, as the general rule
> rather than a case-by-case call.
>
> - **Tier lines do not gate probe cleanup.** Probe cleanliness outranks tier
>   order. The tier law governs which postulates get GROUND; it does not decide
>   whether proven work is allowed a home. Never park an assembly behind a tier.
> - **The receipt route is the fallback.** `-- PROBED <date>:` into a src
>   postulate's header, then delete, is right only for content that cannot be
>   assembled — a measurement, a refutation, a reached-state receipt. Anything
>   with provable content gets assembled instead.
> - **Check the SUBJECT is live before assigning a landing.** "Zero postulates +
>   real theorems + not in src" is necessary but NOT sufficient — a clean proof
>   about something the code no longer does is dead. `Visited-Width-Probe.agda`
>   passed that three-part test and was unassemblable: it bounded a demand
>   against an allowance `3 + 2 * sz` that appears NOWHERE in src, because
>   `capsBase` (Rx/Evaluator.agda:920) deliberately reads `entryCeil` into the
>   tower height instead of bracketing it (Caps.agda:1300-1310 states the
>   rationale; the width conjunct discharges by `k≤towerℕ` and costs no
>   postulate). Its structural content had already landed as `Sub`/`Sub-∷` at
>   Caps-Face:1418. **Deleted 2026-08-09** — wiring it in would have required a
>   vacuous bridge, which is worse than an orphan because it looks discharged.

> **THE SWEEP OF 2026-08-09: 82 → 56 probe files.** Deleted in `8250241`
> (Visited-Width), `109757a` (5), `432a8ad` (10) and `79bec14` (10). Recover any
> of them with `git show <sha>^:agda/probe/<File>.agda`; each commit message
> carries the per-file finding, so `git log` answers "what did that probe
> establish" without restoring it.
>
> The last ten were **receipt probes**: refutations and measurement batteries
> whose conclusion was ALREADY transcribed into a src comment, in full, with the
> numbers. `Depth-Blowup` (`depthE ≤ capsBase` is false), `OpIterD-Budget`
> (`opIterD-budget` at R=0 reads `2 ≤ 0`), `Share-Residue` (refutes the entry
> level at S=2, j=0), `Dep0-Walk` (the depth-zero walk overshoots structurally),
> `Cut-Caches` (the count both TRAILS and LEADS the registry), `Mu-Nest` (the
> measure is `syncSizeᵉ`, not `nestᵉ`), `Charge` (`j ≤ D * cSize` breaches 47
> against 40), `Mint-Loop-Probe` (the false middle step), `Mint-Loop-Frames`
> (103 refl pins that Caps-Face:4172 itself calls "a redundant cross-check"),
> and `Battery-Done-Thread` (a rehearsal whose threading has landed).
>
> **Two process findings from the sweep, both about checks that could not fail:**
>
> - **A probe deletion has TWO ends, and only one was gated.** C1 gates
>   PROBES.txt against the directory; nothing gated the Makefile, so
>   `make visited-width-probe` and `make frame-mint-probe` sat broken (agda exit
>   42) after their files went. Now gated as **(C2)** — any Makefile recipe
>   naming a probe file that does not exist fails the gate, verified by planting
>   one. Also fixed: `make help` had been broken since `bb88f16` by a stray
>   quote in the `width-count-probe` blurb — the documentation surface for every
>   probe target, dead for days, because nothing runs `make help`.
> - **The consumer census had a degenerate row class of its own.** Its
>   name-extraction regex reads top-level `name :` signatures, so a file of
>   ANONYMOUS `_ : … ≡ n` refl pins yields zero names and therefore zero
>   consumers — sorting it to the top of the "nothing uses this" list on a row
>   that could not have failed. Both Mint-Loop files were exactly that shape.
>   The verdict survived on other grounds (no named theorem to land, numbers
>   already in src), but **a census row for a file with zero extracted
>   definitions carries no information — check the extraction before the count.**
>   A second instance of the same class: a name containing `→`
>   (`not-true→false`) falls outside a `[\w\-?]` character class, so the
>   signature never matches and the definition drops out of the count
>   ENTIRELY — `Wf-Aux-Probe` read as "1 theorem, all landed" when it has
>   three, two of them unlanded. Both blind spots err toward "nothing here",
>   which is the direction that gets things deleted. **Re-extract permissively
>   (`^(\S+)\s+:`) before acting on any census row.**
>
> **TEN OF THE THIRTY-THREE PROBES DELETED ON 2026-08-09 DID NOT COMPILE.**
> This is the sweep's most important finding and it outranks every classification
> above it. Eight (`Frame-Work`, `Eval-Growth`, `Hop-Descent`, `J-Budget`,
> `Fold-Count`, `Mult-Width`, `Width-Count`, `State-Blowup`) still
> `open import Verify-Budget-Sufficient`, an umbrella module deleted in `a8508d6`
> when it was split into submodules; agda exits 42, "Failed to find source of
> module". Two more failed on their own: `Count-Level-Probe` on "Multiple
> definitions of `size≤widAt1`" — **it broke because its own content landed** in
> Subscribe-Face:441, which is a positive signal — and `Entry-Caps-Refuted` on a
> genuine type error (`ℕ → Caps !=< Caps`), stale against an API that moved.
>
> Every one of the ten had a live `make` target that would fail. Three
> independent classification sweeps had recommended KEEP for most of them as
> "load-bearing evidence", because all three read headers and citations and none
> ran the file.
>
> **THE RULE THIS ESTABLISHES: a probe's classification is worthless until it
> compiles.** `agda/probe` is outside `make agda` by design — that exemption is
> what makes it cheap — but the same exemption means nothing ever asks whether a
> probe is still true. A refutation that cannot be re-run is not a machine-checked
> receipt, it is a historical artifact, and its only surviving value is the number
> already transcribed into a src comment. **Compile-check before classifying, and
> treat a non-compiling probe as deleted-in-fact.** Repairing one to restore
> "re-runnable evidence" nobody has run since `a8508d6` is the inventory the
> shit-or-get-off-the-pot rule forbids — and two of them cannot be run affordably
> even repaired (`J-Budget` OOMs at 13 GB by design, `Frame-Work` takes ~30 min).
>
> **A DELETION HAS THREE ENDS, AND ONLY ONE WAS EVER GATED.** C1 gated
> `PROBES.txt` against the directory. The other two both broke during this sweep:
> **(C2)** a `make` target whose file is gone — `make visited-width-probe` and
> `make frame-mint-probe` sat broken, and this round's own deletions left 14 more;
> **(C3)** a probe importing a deleted probe — `Charge-Probe` was deleted as a
> "receipt probe" while four live probes imported it for its program families
> (`progD`/`progW`/`pF1`/`pF2`). It is restored, with a ledger line naming that
> role. **A probe is EVIDENCE and INFRASTRUCTURE independently; classify both
> axes before deleting.** Both gates were verified by planting the failure and
> watching them fire, not by observing a green run.
>
> **AND THE METRIC ITSELF WAS MIS-FRAMED AT FIRST.** The census counts names
> defined in a probe that also appear in src, and that was initially read as
> "src consumes this probe". It cannot: `agda/probe` is outside the build and
> src never imports from it, so the number is a NAME COLLISION count, i.e. **how
> much of the probe already landed**. That inverts the worklist — a HIGH count
> means duplicate and is the cheap, safe deletion; a LOW count means unlanded
> and needs judgement. The per-file verdicts held because each was made by
> reading the src comment rather than the number, but the sweep order was
> backwards for several rounds.

## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous       The-Proof.agda:1098 — REAL, module postulate-free
 ├─ batch-agreement                         proven
 └─ evaluate-well-formed                    Verify-Well-Formed.agda
     ├─ budget-sufficient                   Caps-Bridge.agda — PROVEN from:
     │   ├─ burst-wet   ← subscribeE-wet            [T1 risk: walk-core, wet-core]
     │   ├─ burst-caps  ← subscribeE-wet-via-caps   [T1 risk: lift-core, opIterD-core, init-capsOK?]
     │   └─ drain-dry   ← cascade-wet-via-caps      [T1 risk: dry-tick-core, cascadeGo-wet-core, P3, P4]
     └─ THE WELL-FORMEDNESS BRANCH          its own 21 postulates    [T2]
```

**THE CAPS ROUTE DOES NOT REPLACE P1 — IT RESTS ON IT.** Both branches of
`budget-sufficient` route through `subscribeE-wet`: `burst-wet` directly, and
`burst-caps` because `subscribeE-wet-via-caps` takes its `hasDry` and `INV?`
conjuncts straight out of it. No amount of caps work retires the wet contract.

---

## THE RISK LEDGER — every postulate, ranked (2026-08-06 accounting)

Live names and counts come from `make wiring`; this section ranks them. Four
risk classes, worst first:

- **FALSITY** — the statement may simply be false. The worst class: everything
  ground above a false statement is wasted, and the restatement cascades.
- **SHAPE** — the statement is probably true of the right thing but is known or
  suspected to be the WRONG STATEMENT (too weak to consume, wrong hypothesis
  set, imprecise) — a guaranteed future restatement, i.e. deferred falsity.
- **VACUITY** — the statement typechecks but asserts nothing (abstract-helper
  quantification, duplicate types, `⊤`). Zero falsity risk, zero content; the
  risk is REPORTING — it reads as a claim and is not one.
- **DIFFICULTY** — believed true and correctly stated; the risk is only that
  the proof is hard. The cheapest class to carry.

**PROBEABLE means machine-checkable today**: the statement is an equation or
decidable bound over COMPUTABLE functions (`evaluate`, `capsOK?`, `depthE`,
`storeNestMax`, `spec-batchSimultaneous` …), so concrete instances check by
`refl` exactly like the bug cache.

> **CORRECTION (2026-08-06) — THE CAPS AXIS IS NOT PROBEABLE, BY DESIGN.** This
> ledger's first draft listed `opIterD` and the caps arithmetic as probeable.
> That was WRONG. Four symbols on that axis sit in `abstract` blocks —
> `opIterD` (Evaluator:727), `blowH` (Evaluator:898), `sizeCount` (Caps:368),
> and `capsAt` through `sizeCount` — so they never reduce to numerals and no
> `refl` row can ever be written about them. The opacity is DELIBERATE and
> load-bearing: Caps.agda:365 says outright that "whether `.Wet` normalises or
> runs for an hour is decided by whether this symbol stays stuck." On top of
> that, `blowH m = 6 + m + 2 * poolCount (towerℕ m) m` is a tower-of-towers, so
> even unsealed it would not terminate.
>
> **The consequence for the roadmap: Phase 0 cannot reduce the caps axis's risk
> at all.** Those postulates are reachable only by PROOF. But there is a working
> substitute, and it is proven, not speculative: attack them **SYMBOLICALLY** —
> state the full type at symbolic `e`/`ins` in a probe and close it with a lemma
> that never reduces the sealed symbol. That is exactly how
> `three-size≤capsH-core` went from "unprobed postulate" to "one-line proof"
> (#12 below). **Symbolic rehearsal is the caps axis's Phase 0.**

QuickCheck/oracle only ever tested impl≡spec — before 2026-08-06 **no postulate
in this ledger had ever been probed**; closing that blind spot is Phase 0.

### Tier 1 — Verify-Budget-Sufficient (originally 12; #4, #6, #7, #8, #12, #13 discharged — 6 live)

> **STATE, 2026-08-07 morning.** Six of the original ledger are gone. What is
> LEFT splits cleanly in two, and the split is the schedule:
>
> - **The anchor problem — #1, #2, #3, and #11 by inheritance.** All four reduce
>   to the three demand postulates in `Anchor-Dry.agda` (`chainStep-demand`,
>   `foldPath-demand`, `subscribeInner-demand`). Discharging those discharges the
>   block. This is real mathematics — the reachability induction — and it is the
>   critical path.
> - **Two grinds and one refuted kit lemma — #5, #9, #10.** `depth-compositional`
>   is assembled with `storeNestMax-installScan` refuted and being rerouted; the
>   two Caps-Face faces are grinds over kit that already exists.
>
> **UPDATE 2026-08-09.** The Caps-Face half of that second bullet is now
> structural rather than open: the P3 + #9 signature pass landed, #10's
> monolith is a real definition over the single sub-postulate
> `innerFinish-concat-face-go`, and #9's statement carries the two
> hypotheses it was missing. Both faces are now pure grinds over repaired
> statements. The pass added exactly one genuinely new claim,
> `cascade-depth-capsH` — the delivery-side depth bound, which nothing in
> the repo had ever stated. **The anchor problem (#1/#2/#3, and #11 by
> inheritance) is now the whole of tier 1's risk**, and it is where the
> remaining work is.
>
> **UPDATE 2026-08-10 — A DESIGN RULING ON THE ANCHOR, from one abandoned
> landing.** An attempt to discharge `chainStep-demand` / `foldPath-demand`
> by instantiating the proven `Walk` (`.Delivery-Walk`) at the demand
> ledgers was BUILT, TYPECHECKED, AND THEN REVERTED. It typechecked and
> passed `make gate`; it was still wrong. Both reasons are worth keeping,
> because each one closes off a route someone will otherwise re-attempt.
>
> **(1) A CONSTANT DEMAND LEDGER CANNOT BE WALKED.** The instantiation set
> `Vb _ vs = all (valB? Dm Ψ _) vs`, `Bb _ str = burstB? Dm Ψ str` —
> constant in the walk level J, which is what makes `Res.burst` land
> directly on `foldPath-demand`'s conclusion with no widening step. But the
> walk THREADS its ledger through every frame: `sf-step`'s output feeds the
> next frame's input, so a level-constant `Vb` demands that EVERY SINGLE
> FRAME preserve a fixed size bound. It does not. `stepFrame` on `map-f fn`
> is `map (applyFn fn) vals` (Evaluator:1250), and a duplicating `fn`
> (`occsᵗ fn = 2`) roughly doubles `sizeᵛ`; a value admitted at `sizeᵛ = Dm`
> comes out above it. **Dm is not a fixed point of the growth map, so the
> per-frame statement is false even though the per-FOLD statement it was
> derived from may well be true** — Dm's tower is sized to absorb a whole
> instant, not to be idempotent under one frame. The general lesson:
> `Walk`'s `*-widen` fields are not decoration, they are the walk telling
> you the ledger must GROW WITH THE LEVEL.
>
> **MACHINE-REFUTED, same day** (probe deleted at `83b29c1` once this
> receipt was written; recover it from git if it ever needs re-running). `fn = pairᵗ (varᵗ x) (varᵗ x)`, `Dm = 1`,
> `Ψ = 0`, one payload `0 : natᵗ`: `sizeᵛ natᵗ 0 = 1` fits the bound,
> `sizeᵛ (applyFn fn 0) = 3` does not — both by `refl` — so the `Vb` OUTPUT
> conjunct reduces to `false` and the claim closes by `()`. **NOT VACUOUS:**
> all five hypotheses are discharged at `st-init` of a concrete program —
> `walkOK` from `init-capsOK?-base`, the path ledger by `refl`
> (`sizeᵗ fn = 3 ≤ 3`, `occsᵗ fn = 2 ≤ 2`), the payload ledger by `refl`,
> the registry by `refl`, the depth by `z≤n`. Four rows LOAD-BEARING; the
> registry row is DEGENERATE (empty registry at init). **NOT COVERED:** the
> statement at the REAL `Dm = (2·B + 12) · towerℕ (suc sz)`, which is not an
> evaluable numeral — that this Dm is likewise no fixed point of a doubling
> map is reasoning, not a row.  **The probe is DELETED at f08b0bf** — its content is a refutation, so it takes the receipt route (this paragraph IS the receipt) rather than being assembled, and the numbers above are the whole of what it established.  Git history is the archive.
>
> **(2) THE RECURSION WAS NEVER THE OPEN PART — it is already proven, on
> the caps axis.** `foldPath-caps`, `dispatchShare-caps`, `shareGo-caps` and
> `chainStep-caps` (`.Subscribe-Face:3243-3489`) are REAL DEFINITIONS, a
> mutual clique over exactly the same four evaluator functions, each
> concluding `burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true`. So
> re-deriving the fold by a second walk instantiation buys nothing.
>
> **WHAT THIS LEAVES — and it re-aims the anchor.** The real content of
> `chainStep-demand` / `foldPath-demand` is NOT the induction. It is:
>
>   (a) **the caps→wet FLAVOUR BRIDGE.** `valCaps?` bounds `sizeᵛ` against
>       `cSize`; `valB? B Ψ` bounds `sizeᵛ ≤ B` **and** `fnCapᵛ ≤ Ψ`
>       (Measures:4853). The second conjunct is wet-only and has to come
>       from Ψ-invariance (INV?'s `fnCapBounded?`; "Ψ never grows — caseW is
>       substitution-invariant"), not from the caps face at all. This is the
>       same shape as the existing `pathSz? → pathBΨ? → pathB?` bridge
>       (Caps-Bridge:673).
>   (b) **the level arithmetic**, `Caps.cSize (frameStep (j + j′) c) ≤ Dm`.
>
> **AND (b) HAS A WITNESS PROBLEM that decides the shape of the fix.**
> `foldPath-caps`'s Σ reports `j′` with NO bound on it — both its conjuncts
> are monotone in `j′` (`capsOK?-mono`, `burstCaps?-widen` under
> `frameStep-mono-j`), so the receipt is upward-closed in its witness and
> carries no quantitative content on the level. The level bound lives in a
> DIFFERENT Σ, the walk's `Res.hi`. Two receipts, two witnesses — they
> cannot be intersected (this is the same trap recorded for `walkH`'s
> `sf-step` below). **So the fix is one walk instantiation whose ledger is
> CAPS-INDEXED** — `Bb J = burstCaps? (frameStep J c) sl`,
> `Eb J = all (eventCaps? (frameStep J c) sl)`, with `Vb`/`Pb`/`OK` left
> exactly as `walkH` has them — which returns the burst and the level bound
> at ONE witness. Every closure fact it needs already exists
> (`burstCaps?-widen`, `eventsCaps?-widen`, `burstCaps?-∷`), and its
> `sf-step` is `stepFrame-face` (PROVEN) plus ONE new conjunct: **`FrameFace`
> (Caps-Face:4655) bounds the output VALUES and not the emitted EVENTS**
> (`proj₁ (proj₂ r)`), so the events half is the one genuinely missing
> frame-local fact. That is the postulate to state next, and it is the same
> shape the `subscribeInner` face (`siC`) already carries.
>
> **THE RULING THAT FALLS OUT — `Dm` AND THE TOWER ARE NOT ON THE PATH
> FOR THESE TWO.** Chase the caps route to its end and it lands on the dry
> family's own target without ever mentioning `Dm`:
>
>   1. the caps-indexed walk gives `burstCaps? (frameStep lvl c) sl str`
>      with `lvl` bounded, at ONE witness (rehearsed, compiles);
>   2. `cascadeGo-caps` (Caps-Face:4345) already bounds the cascade's level
>      by `sizeCount c d` — it just does not carry a burst conjunct there,
>      which is precisely the hole (1) fills;
>   3. **`capsAt-suc-full` (Caps.agda:893) is `refl`**:
>      `capsAt e sl (suc id) ≡ frameStep (sizeCount (capsAt e sl id) (capsH e sl id)) (capsAt e sl id)`.
>      So `frameStep lvl c ⊑ᶜ capsAt e sl (suc id)` for any `lvl ≤ sizeCount …`,
>      and `burstCaps?-widen` carries the burst up to `capsAt e sl (suc id)`;
>   4. whose `cSize` IS `Ŝ = sizeCapAt e sl (suc id)` — `chainStep-dry` /
>      `foldPath-dry`'s conclusion.
>
> `tick-covers-instant` / `count-covers-tower` stay wired (`subscribeInner-dry`
> still consumes them), but they are NOT needed for these two. **This does not
> make the anchor free — it RELOCATES its content**, off "a demand model with a
> tower-sized constant" and onto "the landing level fits `sizeCount`", which is
> what the entire caps machinery was built to prove. That is a better place for
> it to live: it is the same obligation `budget-sufficient` already carries,
> instead of a second, independent, measured-not-proven numeric model.
>
> **NEXT, in order:** (i) extend the cascade receipt with the burst conjunct at
> the same `j` via the caps-indexed walk — one new postulate,
> `stepFrame-burst-face`, and only its events half is genuinely open;
> (ii) state the caps→wet flavour bridge (the `fnCapᵛ ≤ Ψ` conjunct is wet-only
> and must come from `INV?`'s `fnCapBounded?`, not from the caps face);
> (iii) rewrite `chainStep-dry` / `foldPath-dry` over (i)+(ii)+`capsAt-suc-full`.
>
> **LANDED, same day — with BOTH of the above steps' statements repaired
> first.**  Review of the rehearsed route found v1's two bridging postulates
> mis-stated, each in a canonical broken shape: `burstCaps→burstB` concluded
> `fnCapᵛ ≤ Ψ` from hypotheses carrying NO fnCap information (`valCaps?` is
> size ∧ width only, Caps-Face:674; `INV?` of the output STATE says nothing
> about in-flight stream payloads) — the conclusion-from-no-hypothesis
> anti-pattern; and `fold-level-fits` lacked the `plen`/`gas` guards, so at
> unbounded `plen` its base `iterL plen 0` outruns the fixed `sizeCount c d` —
> false by instantiation.
>
> **The repair (v2, `Verify-Budget-Sufficient/Burst-Walk.agda`) rests on one
> observation: `valB? B Ψ`'s two conjuncts have OPPOSITE characters.**  The
> SIZE half grows per frame (the constant-Dm refutation) and rides the walk's
> caps level; the FNCAP half is frame-invariant ("Ψ never grows") and rides
> CONSTANT.  The walk carries the conjunction; `Res.burst` returns both
> flavours; they recombine pointwise into `burstB? (cSize c′) Ψ` as a REAL
> PROOF (`burstB?-halves`).  And stating the receipt at the CASCADE level
> (walk entered at J = 0) makes the landing-level bound `cascadeGo-caps`'s own
> arithmetic, cribbed term for term — `fold-level-fits` is GONE, not repaired.
>
> **Net effect on the ledger:** `chainStep-demand`, `foldPath-demand`,
> `chainStep-dry`, `foldPath-dry` all DELETED; `cascadeGo-burst-dry` is a REAL
> DEFINITION (Burst-Walk § 7) consumed by `dry-tick-core`'s telescope; the ONE
> new postulate is `stepFrame-burst-face` (Burst-Walk § 2), whose
> walkOK/valsCaps?/pathSz?/level conjuncts ARE the proven `FrameFace` at the
> same witness — genuinely open are its emitted-EVENTS caps half and its Ψ
> halves (the wet face of one frame, from-inner/thru-outer cases being the
> same family as `subscribeInner-demand`; whichever is discharged first should
> absorb the other).  `fnCapB-latch`/`fnCapB-finish` and every walk closure
> fact are real proofs.  frameBΨ?/pathBΨ?/regsBΨ? relocated from Caps-Bridge
> to Burst-Walk (import direction).  If the eventual dry-tick grind needs
> per-chain receipts mid-cascade, they come from re-entering the same walk at
> the mid-cascade level; the cost that reappears then is the nonzero-base
> level bound — v1's `fold-level-fits` repaired with `suc plen ≤ S` and a gas
> guard.
>
> **THEN SPLIT, same day (2026-08-10) — `stepFrame-burst-face` is no longer a
> postulate.**  It is a REAL ASSEMBLY (`Burst-Walk` § 5b) over the PROVEN
> `stepFrame-face` (Caps-Face:4678) plus five per-frame WET leaves, of which
> `map-f` is proven.  Four of the assembly's six obligations come off ONE
> `stepFrame-face` call: the level bound and `capsOK?` verbatim, `valsCaps?`
> verbatim, and `regP? (pathSz? …)` via `capsOK?-regs` on that same `capsOK?`.
>
> **The decomposition rule that made it work, and the trap it avoided.**  The
> Ψ conjuncts are FRAME-INVARIANT, so `j′` does not appear in them — they can
> be stated once, level-free.  The emitted-EVENTS caps half is NOT: a step can
> build values that only fit the grown level, so stating it at `J` would have
> been the FOURTH mis-stated bridge on this route.  So `WetFace` took `j′` and
> the two caps receipts as HYPOTHESES, passed in verbatim from the assembly's
> own `stepFrame-face` call.  Nothing is re-derived and nothing is guessed.
>
> **SUPERSEDED SAME DAY — the events caps half was STILL on the wrong face,
> and the fourth mis-stated bridge had in fact been built (2026-08-10,
> later).**  Taking the receipts as hypotheses dodged the false-at-J trap but
> left the conjunct demanded at a UNIVERSAL j′ whose only witnesses are
> state/vals receipts — and an emitted root delivery is pinned by NEITHER: a
> program whose inner delivers one large root value while its post-state
> stays small meets every hypothesis at j′ = 0 and fails the conclusion.  So
> `wet-innerFinish`/`wet-thru` as first stated were unprovable (and likely
> false).  Caught by census before any grind: the conjunct's only true
> suppliers — `innerFinish-caps` and `subscribeInner-caps` (Subscribe-Face,
> ZERO postulates, the whole caps clique proven) — mint it at the SAME j′ as
> the state receipts, and `FrameFace` (the only route that witness travels)
> was DROPPING it.  **Repair: `FrameFace` gained the events conjunct** (its
> producers all pay: `[]`-emitting clauses `refl`, take `takeDispatch-caps`'s
> own third conjunct, P3/P4 postulates strengthen automatically because they
> conclude `FrameFace` by name and their named suppliers already report it),
> **and `WetFace` became Ψ-PURE** — no caps, no level index, no growth
> witness anywhere.  The two open wet leaves now say only that one frame
> PRESERVES the Ψ ledger, the same invariant `INV?`'s Ψ half claims for whole
> subscribes: their proof is the Ψ mirror of Subscribe-Face's proven caps
> clique, with the gas edge into `subscribeE` as the one real recursion.
>
> **Then all three STATE-LOCAL leaves were proven, same day.**  `wet-take`
> (§ 2.4b) and `wet-scan` (§ 2.4c) joined `wet-map`, each on the first fill
> attempt, because the split had already put every obligation where an
> existing lemma could reach it:
>
> - **take** — `takeVals-Ψ` mirrors `takeVals-caps` clause for clause;
>   `cutThrough-keptP` is stated for a GENERAL path predicate (the caps side
>   wants the same fact and can crib it); `fnCapNode Ψ (take-st _)` is `true`
>   outright.  (The events CAPS half was closed here by
>   `cutThrough-closes-caps` while it still sat on the wet face; after the
>   FrameFace move below it rides the caps side, where `takeDispatch-caps`'s
>   own third conjunct supplies it.)
> - **scan** — cribbed from `stepFrame-scan-wet` (Wet:441), the same clause
>   proven against the capᴱ ledger.  One difference worth recording: the caps
>   half is NOT re-derived (the assembly holds it), so the leaf needs only the
>   fnCap half of the node lookup — `lookupNode-fnCap`, not the two-sided
>   `lookupNode-B`, whose `boundedNode` premise nothing at this level can pay.
>   **Splitting a two-sided lemma to take only the half you can pay for is the
>   move**; carrying the other half would have forced caps facts down into a
>   leaf that has no business holding them.
>
> **Then the two *All edges were split too, and one of the two splits was
> REJECTED — the rejection is the more useful result.**
>
> - **from-inner SPLIT (kept).**  `innerReact` passes its payloads through
>   UNTOUCHED on two of its three paths — not-finished (`fin = false`) and
>   ABSORBED (`fin = true` but a registration under this inner is still live,
>   so the completion is swallowed).  Both are proven; the leaf reduces to
>   `wet-innerFinish`, with `fin` pinned to `true` and the absorb test already
>   resolved.  `wet-pass` generalises `wet-nil` to carry a payload list.
> - **thru-outer SPLIT (rejected, and here is why).**  `thruWrap op nid fin
>   (thruWalk …)` looks like the same shape — the walk subscribes per payload
>   (real content), the wrap only sets a node's `done` FLAG — and **the wrap is
>   indeed fnCap-TRANSPARENT**: payloads/events/schedule pass through, three of
>   the four rewritten nodes have `fnCapNode ≡ true` outright, and
>   `concat-st`'s measure reads the queue `q`, which the rewrite does not
>   touch.  But the assembly states its two caps receipts at the WRAPPED
>   result, and `proj₁ (thruWrap …) ≡ proj₁ (thruWalk …)` is NOT definitional —
>   recovering it needs the same 26-branch case split the transparency proof
>   does.  A `wet-thruWalk` leaf would therefore either carry hypotheses about
>   a tuple it is not about, or pay for a transport buying no risk reduction.
>   **The transparency finding is recorded as a receipt in `wet-thru`'s own
>   header** so the eventual proof disposes of the wrap in one step instead of
>   rediscovering it.  This is the receipt route working as intended: the
>   knowledge lands, the file does not.
>
> **THEN THE FROM-INNER EDGE WAS DISCHARGED ON TOP OF THE REPAIR (2026-08-10,
> same session).**  With `WetFace` Ψ-pure, `wet-innerFinish` became provable
> and was proven — a REAL DEFINITION (§ 2.4e), green on the first fill:
> merge/switch/exhaust rewrite one node field on which `fnCapNode` is `true`
> outright (`setNode-fnCap` + `fcB-live`/`fcB-nodes`); every mismatched
> (op, node) read is the evaluator's catch-all pass (`wet-pass`); and
> concat+yes goes through `concatDrain-Ψ`, a PROVEN walk (one
> `subscribeInner-Ψ` receipt per queued inner, residue-queue bound threaded,
> `all-++-intro` for the appends).  The one postulate left underneath is
> **`subscribeInner-Ψ`** — the Ψ face of `subscribeInner`, mirroring the
> PROVEN `subscribeInner-caps` with every caps conjunct dropped: constant
> bound, no growth witness, no existential.  Its `g0` clause is immediate;
> its `gs` clause is the descent into `subscribeE` — the honest recursion,
> to be ground where `subscribeE-caps` was.
>
> **Open surface now: `subscribeInner-Ψ`, `wet-thru`, `subscribeInner-demand`.**
> All three bottom out in `subscribeInner`/`subscribeE`.  `wet-thru` is now
> a MECHANICAL mirror away from closing: `thruConsume-Ψ` (four ops, each a
> node dispatch around `subscribeInner-Ψ` — mirror `thruConsume-caps`,
> Subscribe-Face:1315), `thruWalk-Ψ` (a list walk shaped exactly like
> `concatDrain-Ψ`), the fnCap-transparency of `thruWrap` (receipt in
> `wet-thru`'s header), and the assembly.  New Ψ kit it needs beyond § 2.4e:
> `mergeBump`'s fnCap face, `switchKill`'s (both `cutThrough-keptP` +
> `sweepLive-fnCap` shapes, already in tree), and concat's queue-APPEND
> bound (`all-++-intro` again).  This is now delegable grind — the pattern
> is established twice over.
>
> **The postulate count went UP by one, net, and this is the mechanism
> working:** one monolith that hid five unrelated obligations became two named
> leaves plus three real proofs.  Had the leaves not been named first, the
> three easy clauses would have stayed buried behind the two hard ones.
>
> **`siC` is a PARAMETER, not an import.**  `stepFrame-face`'s own first
> argument is the subscribeInner caps face; its supplier
> (`subscribeInner-caps`, Subscribe-Face:951, PROVEN) lives in the 44-minute
> module, so importing it into Burst-Walk would cost that module its fast loop.
> `Caps-Bridge` imports both sides and applies it at the `dry-tick` call site.
> The hand-retyped `SiCFace` was machine-checked against the real supplier by a
> coercion line before landing — the one thing that could have silently broken
> the landing.
>
> **One gate lesson, recorded because it cost a red gate.**  `make
> wiring-gate`'s (B4) span collector blanks comment lines and stops at the
> first empty one, so **a comment inside an assembly's argument list silently
> truncates its argument set** and reports everything below it as a stale
> ledger entry.  Keep `dry-tick`'s argument list contiguous; the explanation
> goes above the definition.
>
> The discharges of #6 and #7 have a common shape worth naming: **both postulates
> carried a pile of leading hypotheses that the eventual proof did not use.**
> #6 shed seven expression-level lemmas (its proof is pure level arithmetic);
> #7 shed eight scaffolding facts (`scripted`'s own type index closed the branch).
> Sixteen definitions were swept as superseded across the two. When a `-core`'s
> hypothesis list looks like a route, treat it as a HYPOTHESIS about the route,
> not as a specification — and check whether the direct proof needs it at all
> before grinding through it.

> **THE ANCHOR DESIGN RULING (2026-08-09, design session).** The three demand
> postulates do NOT need a new mutual induction — **the induction is already
> built and proven: it is `Delivery-Walk`.** The ruling, in full, because it
> re-scopes the whole anchor block:
>
> 1. **Why the demand statements are not directly inductive, and why that is
>    already solved.** `chainStep-demand`/`foldPath-demand` hypothesize inputs
>    at `B` and conclude at `Dm` — but `foldPath (f ↠ path′)` feeds each
>    frame's GROWN output back in as the next frame's input, so a fixed-bound
>    mutual induction can never close on itself (the IH's `valB? B` hypothesis
>    is violated one frame in). This is EXACTLY the problem the 2026-08-02
>    walk repair solved on the caps axis (`Entry-Caps-Refuted`): growth is
>    REPORTED as a level climb, not denied. And the walk already threads the
>    level-indexed values ledger through every clause — `sf-step` CONCLUDES
>    `Vb (J + j′) (proj₁ r) ≡ true`, the frame's outputs bounded at the
>    landing level. The hard axis is DONE. It is just never read out.
>
> 2. **The one missing piece: `Res` drops the emits on the floor.**
>    `foldPath`'s root clause packages `evs ++ map value vals ++ [complete]`
>    into the delivery envelope, and `Res` (lvl/lo/hi/good/cnt) says nothing
>    about `proj₁` of the run. Meanwhile `burstB? B Ψ = all emits, all events,
>    eventB?` and **`eventB?` is `true` on everything except `value v`**
>    (Measures:4857-61) — so the burst bound over the output stream is
>    precisely: the packaged `vals` under `Vb`, plus the threaded `evs` under
>    an event ledger. Both are one field away.
>
> 3. **The extension (grind-shaped, the same class as the depth pass that
>    just landed — new premise + new conclusion threaded through the same
>    four clauses):**
>    - `Walk-Hyps` gains an event ledger `Eb : ℕ → List (InstEvent (Val Γ t))
>      → Bool` with widening + `++`-closure fields; `sf-step`'s Σ-conclusion
>      gains `Eb (J + j′) (proj₁ (proj₂ r)) ≡ true`.
>    - `foldPath-go` gains premise `Eb J evs ≡ true` (chainStep seeds
>      `close`/`[]` — bookkeeping, free at any eventB?-shaped instantiation).
>    - `Res` gains a `burst` field: every emitted envelope's events bounded
>      at `lvl` (value events read through `Vb`). Root packages hV/hE
>      widened to lvl; share-sink's handoff is bookkeeping + the fanout's IH;
>      the frame clause is `++`-closure at the widened level; shareGo/
>      cascadeGo cons is `emits ++ rest` — FP's burst widened along
>      `Res.lo REST`, then `++`-closure.
>    - Existing consumers stay cheap: Caps-Face's three `cascadeGo-*`
>      instantiations may set `Eb _ _ = true`, making every new obligation
>      refl-shaped, and simply not read the new field.
>
> 4. **The demand instantiation** extends Caps-Face's existing one (same OK/
>    Pb/Vb — they are already the right ledgers) with a real `Eb`, and reads
>    the new `burst` field: every emitted value ≤ the size at the landing
>    level. The demand postulates then follow from ONE new arithmetic
>    obligation — the numeric bridge `size at (lvls … J₀ (delivN …)) ≤ Dm` —
>    stated as a postulate FIRST (outside-in), sourced from the Tick-Headroom
>    kit (`count-covers-tower`/`tick-covers-instant`). If the walk's natural
>    landing form does not match `Dm = (2B+12)·towerℕ(suc sz)`, RESTATE the
>    demand postulates' numeric form and keep the dry family's Ŝ conclusions
>    fixed — Anchor-Dry is impl-layer, not spec.
>
> 5. **What is genuinely open AFTER the extension — the funnel.** `sf-step`'s
>    discharge for `from-inner`/`thru-outer` frames re-enters `subscribeE` —
>    the subscribe side, #1's territory (`subscribeE-walk-core`, whose
>    Measures:5786 conjunct is exactly a `burstB?` on the subscribe-side
>    output). `subscribeInner-demand` reads off that same face directly. So
>    the extension reduces all three demand postulates, #2, and #3 to **one
>    open surface: the subscribe-side burst face** — which is the postulate
>    PROOF-STATE already ranks riskiest. Consequence, per de-risk mode:
>    **probe #1's statement for falsity BEFORE grinding the extension's
>    instantiation** — a refutation there moves the ground everything above
>    lands on. And restart the `Demand-Battery` probe (open item (c)) for
>    chainStep/foldPath-demand falsity first of all; it is the cheapest
>    unmanaged risk in the block.
>
> Work order: (i) Demand-Battery probe (falsity, cheap); (ii) the walk
> extension grind (worker-shaped: Delivery-Walk + trivial-Eb patches to
> Caps-Face); (iii) the numeric bridge stated as a postulate + the demand
> instantiation assembled over it; (iv) the subscribe-side face — the last
> real mathematics in tier 1.

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `subscribeE-walk-core` | Measures.agda (was :5750) | **ASSEMBLED IN SRC (REAL DEFINITION) 2026-08-11** | **ASSEMBLED IN SRC 2026-08-11**: converted from a single monolithic postulate to a structurally-recursive real definition (structural recursion on `b : Closed Γ u` / `g : Gas`). The definition dispatches all 13 constructors of `Closed` and routes to 26 per-clause and shared sub-postulates. The probe `Walk-Core-Assembly-Probe.agda` (EXIT=0, 2026-08-11) validated the assembly's shape before landing. The ledger grew by design: one vague postulate became 26 specific ones (§1 shared arithmetic: 8 postulates, §2 per-clause: 7 postulates, §3 *All clauses: 3 postulates, §2b μ-specific: 6 postulates, plus 2 proved lemmas and 2 proved helpers). Sub-postulates consume the formerly-deferred `walk-hyps-splitAnchor`, `walk-hyps-round3b`, and `spendᴱ-compose` as explicit parameters. Probe file (`Walk-Core-Assembly-Probe.agda`) pending deletion by design session. |
| 2 | `cascadeGo-wet-core` | Wet.agda:4499 | **DIFFICULTY** | P2's entire content (its only hypotheses are two stBounded? preservation facts). The anchor problem on the cascade axis. The naive per-chainStep decomposition is machine-refuted (`caps-frame-boundary-absurd`). PROBED-GREEN 2026-08-11 on root-path chains (hasDry: confirmed no dried events; INV?: degenerate on tested shapes); from-inner/thru-outer paths NOT COVERED (abstract Gas). No refutation found — reclassified from FALSITY to DIFFICULTY. The INV? conjunct through subscribeE calls is the genuinely open question; it mirrors what cascadeGo-caps (Caps-Face:4345) already proves. |
| 3 | `subscribeE-wet-core` | Wet.agda:4311 | FALSITY, conditional | Given the walk it is "the outer instantiation" — but the instantiation must manufacture the walk's G/ℓ/Ω entry data from `INV?` alone, and the INV?/capᴱ flavor conversion is unchecked. Moderate incremental risk over #1, with maximal blast radius (both branches of budget-sufficient). |
| 4 | ~~`sub-charge-capsOK-lift-core`~~ | — | **DISCHARGED 2026-08-06 — the postulate is a REAL PROOF; the risk moved into #13 and one Phase-3 obligation** | The general-id depth bound (the residual design question recorded here) was RESOLVED as a THREADING ruling, not a lemma: `depthE g b κ id now sched st ≤ capsH e sl id` is a RUN INVARIANT — the unconditional form is FALSE (Depth-Bound's header: a long map-f chain over a tiny `e` breaks any state-free `depthE ≤ capsH`), and "reachable" is not first-class here, so the bound enters as a PREMISE (`depOK`) exactly as `nestOK`/`opsOK` did, discharged at `burst-caps` by `depthE≤capsH-root` and owed at general call sites by the Phase-3 induction (see the depOK preservation obligation, Phase 3 item 5). **Why the depth-capped route could never work off the root, recorded so nobody re-attempts it:** the state at counter `id` satisfies `capsOK?` only at `capsAt e sl id`, whose `cSize` is tower-sized (`capsAt-tower`: `cSize ≤ towerℕ (capsH)`), so `depth-capped` yields `dep ≤ 3·towerℕ(h)` against a target of `h` — off by "towerℕ of" at EVERY index; no index shift closes it. `depth-capped`'s role is confined to the root, where the SMALL `baseCaps` satisfies `capsOK?`. **With depOK threaded, every link of the old route comment became an existing lemma** — jB → `opIterD-dominated` (k≤S/m≤S from nestOK/opsOK, `2≤capsAt-size`/`1≤capsAt-reg` free) → `sizeCount-body` + record eta → `sizeCount-mono-d` (#13, the ONE new postulate) over depOK → `frameStep-mono-j` → `capsAt-suc-full` → `capsOK?-mono` — and `sub-charge-capsOK-lift` is now a ~20-line real definition in Caps-Bridge. Kit fallout: `capsAt-suc-full`/`frameStep-full`/`frameStep-mono-j`/`depthE≤capsH-root`/`opIterD-dominated` all kept real consumers; `⊑ᶜ-refl`, `frameSz?-⊑` (Caps-Face) and `prepend-fits` (Subscribe-Face) were speculative kit the proof never needed — DELETED 2026-08-06 (this commit; git is the archive). |
| 5 | `depth-compositional` | **Depth-Compositional.agda (LANDED from probe 2026-08-06; kit ground 2026-08-07)** | **ASSEMBLED IN SRC; 7 of 8 kit lemmas PROVEN (`943e690`); the 8th — `storeNestMax-installScan` — REFUTED** | The worker grind proved the three burst-zero lemmas, installTake, and the three size-arith lemmas, and REFUTED `storeNestMax-installScan`: `caseᵗ` duplication gives `sizeᵛ (evalTm seed) > sizeᵗ seed`, and evalTm blowup is tower-shaped, so the additive form is unrepairable and no linear `scan-size-arith` RHS absorbs it. **The theorem is plausibly still true** — the subscribe-side mirror never reads a freshly-installed scan node's value (accumulators are read at DELIVERY, census finding (2)) — so the repair is an install-invariance lemma rerouting the scanᵉ clause through the ENTRY store (task #49; if some subscribe-side clause DOES read scan values, this escalates to a possible statement refutation — probe with a duplicating seed first). Remaining open here: the 3 BUCKET-(d) postulates + #49. |
| 5° | (superseded row) | — | (was: assembled over 3 postulates + 8-lemma kit) | The monolithic postulate is gone from Depth-Bound: `depth-compositional` is now a structurally-recursive real definition in its own module (per the SCC-granularity rule), dispatching to `depth-conn-storeNest` / `depth-all-bound` / `depth-μ-bound` (the three schedule-blockers, each with its obstacle and route in its header) plus the burst-zero / installNode / size-arith kit (8 small postulates, each one lemma's worth). The `storeNestMax` measure moved with it (Depth-Bound would otherwise import its own consumer). Probe file deleted with its LANDING line per the ratchet. The ledger GREW by design: one vague postulate became 11 specific ones, each separately attackable. |
| 5′ | (probe evidence for #5) | — | **PROBED-GREEN 2026-08-06, evolved states included** | Its census (source comment, point 4) needs `storeNestMax` at the EVOLVED state dominated by the entry bound. **That direction was actually tested**, not dodged: `Depth-Compositional-Probe` drains N real cascades through the evaluator (k ≤ 4, N ≤ 10) and reads `depthE` off the extracted scan accumulator — evolved states, all rows hold. `agda/probe/Battery-Depth-Iter.agda` adds two things: the `switch-st`/`exhaust-st` branch of `depthAll`, which **no prior depth probe had ever exercised** (4 programs, green), and the preservation step `storeNestMax(post-subscribeE) ≤ sizeᵉ e + storeNestMax(pre)` — census point 4's exact inductive step — confirmed at N=1. Thin at N=1, but this is the one tier-1 axis where probing works, and it held. |
| 6 | ~~`opIterD-budget-core`~~ | **Op-Budget.agda (NEW)** | **DISCHARGED 2026-08-07 (`ac77b7e`) — a REAL PROOF, zero postulates, and the gas corner is now a NUMBER** | The residual-budget invariant is proven end to end and lives in its own module. **Two normal forms:** the climb is `TAIL^m ∘ (sLvlD k ∘ J₀)^m` (tails already lvls-dominated by the proven `fIterD-lvls`), and by the proven `dWalkᶜ-front` the budget is `regAt`-many iterations of [one dLvl-step, then a full gas-(g−1) budget from the level reached]. **One round costs FIVE walk positions:** two for the jump (`jump-2step`), one to absorb the entry's G-closure (`G-absorb` — a position spent as raw LENGTH cannot double as the sub-climb's walk), one whose sub-budget hosts the (g−1,k−1) sub-climb, one for the tail (`round-tail-glue`). The m-vs-positions tension (m′ exponential in the level, positions linear) is resolved by `boost-5x`: positions are counted at the BOOSTED level. **The load-bearing discovery was that the walk value at p positions IS the p-th restart level** (`walk-spend`/`walk-spend-many`), so each round's conclusion is the next round's hypothesis verbatim, with no residual bookkeeping. **THE STATEMENT REPAIR — the guard is `3 + k ≤ S`, not `k ≤ S`, and all three units are accounted:** cDel's gas is `suc S`; one unit unfolds `dCapᶜ` into the top WALK; one DESCENDS into a position, because level 0 has only `regAt S R 0 = R` positions and **R may be 1** — the descended level A₁ = `dLvl S W d 0` has `regAt ≥ suc (A₁·S) ≥ 5·S` (`5≤dLvl0`, two iterL unrollings); and `walk-paid`'s own `2 + k` is irreducible, because at k = 0 the entry still spends `G-absorb`, which rests on `tail-fits`, which a gas-1 sub-budget PROVABLY cannot pay. So the guard is not slack the scheme happens to want — it is what the recurrence costs. **The repair's one-unit cost at the consumer is PAID, not deferred:** `capsAt-base-size⁺` (Caps-Bridge) gives `3 + sizeᵉ e + slotsSize sl ≤ cSize (capsAt e sl id)` because capsAt's base is a `frameBlowup`, `2≤sizeCount` says a sizeStep runs, and one `sizeStep S S = S * suc (2 * S)` already clears a `suc`. **Fallout:** `opIterD-budget-core`'s seven expression-level hypotheses are gone — the proof never reaches the expression level — orphaning six proven lemmas (`entry-to-index`, `residAt-connected`, `share-step-resid`, `mu-1≤k`, `mu-step-le`, `k-raise`); ruled SUPERSEDED and swept (`mu-step-le` was already recorded as superseded by `mu-step` at Subscribe-Face:3118). The earlier `1 ≤ R` refutation stands and is recorded in the new assembly's header: at R = 0 the registry walk is empty, `cDel (caps S W 0) d = 0`, and the claim read `2 ≤ 0`. |
| 7 | ~~`init-capsOK?-base-core`~~ | **Init-Caps.agda (NEW)** | **DISCHARGED 2026-08-07 — a REAL PROOF, zero postulates** | All five `capsOK?` conjuncts proven at `baseCaps` / `st-init`. (2), (4), (5) fall to the emptiness of the initial registry and node table. (1) is `all-concat-tab` over `mkHot-bounded`. **(3) was the open branch, and `scripted`'s own index closes it:** `scripted` carries `{ok : T (isData t)}`, and the new structural family `outWᵛ/dWᵛ/pWᵛ-data-zero` shows every data type has `pWᵛ ≡ 0`, so the width check reduces to `0 ≤ᵇ cWid`; cold and shared slots contribute no live source at init at all. The proof BYPASSES the -core's eight scaffold hypotheses — they were kit for a route it does not take — and `baseCaps` moved out of Caps-Bridge with it, so the module is self-contained and solo-checks in seconds. `init-capsOK?-base` is exported through an `abstract` alias: it sits on the budget-sufficient spine, where an unfoldable body is what OOMs VWF. |
| 8 | ~~`init-capsOK?-suc`~~ (was `init-capsOK?`) | — | **DISCHARGED 2026-08-06 — proven at EVERY id, zero new postulates** | The recorded blocker (`capsAt e ins id` never reduces to a numeral because `sizeCount` is `abstract`) killed only the COMPUTATIONAL route. The monotonicity route never needs a numeral: `capsAt-⊑-suc` proves `capsAt e ins id ⊑ᶜ capsAt e ins (suc id)` by spanning `frameStep 0` (= the caps itself, `frameStep-0`) to the full endpoint (`frameStep-full`) with `frameStep-mono-j` at `0 ≤ sizeCount`, and `init-capsOK?` is then a two-clause induction: base `init-capsOK?-0` (rests on #7), step `capsOK?-mono` along `capsAt-⊑-suc` — the initial state never changes, only the caps widen. One Agda footnote worth keeping: the count had to be pinned by hand (`z≤n {n = sizeCount …}`) because `iterSize`/`iterFold` match on it, so unification cannot invert the `⊑ᶜ` endpoints — caught in the fast loop by checking Caps-Bridge against cached interfaces BEFORE paying the heavyweight recheck. Residual risk here is exactly #7 (`init-capsOK?-base-core`), nothing else. |
| 9 | ~~`thruOuter-face-core`~~ (P4) | **Caps-Face.agda — now a REAL DEFINITION** | **DISCHARGED 2026-08-11 (`0b9cca9`)** | Probe body (`ThruOuter-Face-Core-Probe.agda`, EXIT=0) promoted to `abstract` real definition via the private-impl + abstract-alias pattern. Private helpers inline Subscribe-Face's `thruConsume-caps` / `thruWalk-caps` walk machinery against a `siC` hypothesis (instead of a direct import), so the 44-minute module stays off the import chain. Two new module imports: `Caps-Chain` (walk-nil, inner-nil, walk-index, frame-step, queue-push) and `Caps-Sadd` (walk-step-suc). The original doubts about the second-number receipt and `fCharge` compatibility were resolved by the repaired statement's `suc (depthWalk …) ≤ d` premise threading — the grind closed in the probe. Sealed `abstract` per the VWF-spine rule. |
| 10 | ~~`innerFinish-concat-face-core`~~ (P3) | **Caps-Face.agda — now a REAL DEFINITION** | **ASSEMBLED 2026-08-09; the monolith is replaced by ONE sub-postulate** | The probe's assembly landed and the signature pass that unblocked it is done (see the block above the table). `innerFinish-concat-face-core` is a real definition whose body is a single call to **`innerFinish-concat-face-go`**, the one remaining gap: it takes the node read `nd : Maybe (NodeState Γ)` **explicitly**, which is load-bearing rather than cosmetic — writing the dispatch as a `with w ≟ᵗ s` inside the assembly makes `dpt` reduce to `suc (depthDrain …) ≤ d` while re-evaluating `depthFin` on a VARIABLE `s` yields `depthFinC … (s ≟ᵗ s) ≤ d`, and `s ≟ᵗ s` is not definitionally `yes refl`, so the two types never meet. With `nd` an argument there is no with-abstraction between the assembly and the premise and the types are literally the same expression. `-go` owes seven trivial node cases (`innerFinish-face-keep` at j′ = 0) and ONE real obligation, the concat+yes drain through `innerFinish-caps` (Subscribe-Face:1761) — which is precisely what H1 and H2 were added to feed. **The five kit hypotheses are passed straight through rather than dropped**, eta-expanded (bare they leave unsolved metas); dropping them would orphan `burstCaps?-∷` and the four `*-slots` transports. |
| 11 | `dry-tick-core` | Caps-Bridge.agda:439 | DIFFICULTY | Given `cascadeGo-wet` (its first hypothesis) it is latch/finish bookkeeping plus the Deliveries counts. Nearly all its risk is inherited from #2, not its own. |
| 13 | ~~`sizeCount-mono-d`~~ | **Level-Mono.agda (NEW)** | **DISCHARGED (task #46) — REAL PROOF, zero postulates** | `sizeCount c` is monotone in its depth-fuel argument. Proven via the mutual monotonicity grind over the fLvlD SCC through its exported clause equations (`fLvlD-0`/`fLvlD-suc`/`fIterD-0`/…). Imported into Caps-Bridge via `open import Verify-Budget-Sufficient.Level-Mono using (sizeCount-mono-d)` (Caps-Bridge:99). PROOF-STATE was stale — the proof was complete but the row was not updated. |
| 12 | ~~`three-size≤capsH-core`~~ | — | **DISCHARGED 2026-08-06 (`559780a`), then re-shaped (`2d4b899`)** | `three-size-le-blowH` + a 7-lemma support chain landed in `Caps.agda`; the postulate is gone and `three-size≤capsH` is a real definition. `S≤sizeStep` was deleted with it (its sole consumer was the replaced hypothesis slot). **Then it nearly died twice by accident** — a worker deleting the superseded root chain stranded `three-size-le-blowH`, and a second worker proposed deleting THAT. Both times the orphan report was right and the ruling was wrong: it is one half of the depth composition (`depth-capped` gives `depthE ≤ 3·cSize`, this gives `3·cSize(base) ≤ blowH`), and the two chain to `depthE ≤ capsH e ins 0`. Now wired root-first: `three-size≤capsH` → `depthE≤capsH-root` → hypothesis of `sub-charge-capsOK-lift-core`. **The lesson is general: a consumer-count sweep cannot tell a dead lemma from an unconnected half of a composition. Read what an orphan SAYS before ruling on it.** |

> **THE P3 + #9 SIGNATURE PASS IS DONE (2026-08-09).** Item (b) below is
> closed. What it cost and what it bought, because the shape generalises:
>
> - **It was WIDER than "seven signatures".** Row 10 scoped the pass as
>   `innerFinish-concat-face` → … → `caps-tick`. In fact H2 has to reach
>   `Walk-Hyps.sf-step`, which quantifies over an ARBITRARY frame — so the
>   premise threads through the walk's whole mutual block (`foldPath-go`,
>   `dispatchShare-go`, `shareGo-go`, `cascadeGo-go`) in `Delivery-Walk`,
>   not just through `Caps-Face`. Three modules, not one.
> - **But it was SHALLOW, because the depth mirror is DEFINITIONALLY equal
>   at every hop.** `depthFrame … (from-inner …) … fin = depthReact … fin`;
>   `depthReact … true = depthFin … (lookupNode …)` — literally H2 as the
>   probe stated it; `depthReact … false = 0`, so the absorbed branch is
>   free. Up the walk it composes by `⊔`: `depthFold … (f ↠ path′) …
>   = depthFrame f … ⊔ depthFold path′ …`, and the tail's arguments are the
>   very terms `foldPath-go` already recurses with. So every discharge is a
>   `≤-trans` with a `⊔` projection and NO transport anywhere.
> - **`lub3-l/m/r` (Caps-Depth) were already there for exactly this**, with
>   the standing warning that `⊔` bounds must be NAMED (`_⊔_` is a defined
>   recursive function, so an unnamed bound turns the projection into an
>   inversion Agda cannot solve — the 2026-08-05 Stage-A failure).
> - **NEW: `depthCascade` (Caps-Depth), and it is deliberately BRANCH-FREE.**
>   The honest measure would skip a cancelled chain by testing
>   `any (_≡ᵇ rid) (EvalSt.cancelled st)` — but `cascadeGo-go` already
>   with-abstracts that scrutinee, and **a with-abstraction does not rewrite
>   the type of an already-bound hypothesis**, so the premise would be
>   stranded in every branch. `depthShareGo` had solved this before and its
>   comment says so: report the tail at BOTH states, land in `a ⊔ (b ⊔ c)`,
>   and let the consumer read its case off a projection. Copied verbatim.
> - **THE ONE GENUINELY NEW GAP: `cascade-depth-capsH` (Caps-Face).**
>   `depth-compositional` (row 5) bounds `depthE`, the SUBSCRIBE side, and
>   **nothing anywhere bounds the DELIVERY side** — `depthCascade` reaches
>   frames through `chainStep`/`foldPath`/`stepFrame`, all outside `depthE`'s
>   induction. So this is a real statement, not a repackaging, and it is the
>   delivery-side twin of `depthE≤capsH-root`. Conditioned on `capsOK?`
>   deliberately: the unconditional form is false for Depth-Bound:11's reason.
> - **H1 was free**, as row 10 predicted: `capsAt-base-size` already has
>   `slotsSize sl` as a summand of `cSize (capsAt e sl id)`.
> - Three Agda mechanics worth keeping: a `where` block is **not** mutual
>   (referencing a binding defined further down is a scope error, not a
>   forward reference); stdlib's `m≤n⊔m : ∀ m n → n ≤ m ⊔ n` puts the
>   SUBJECT second; and the five kit hypotheses must be **eta-expanded** at
>   the call site or their implicits go unsolved.

> **OPEN AT SHUTDOWN (2026-08-07 morning; (a) and (b) both CLOSED 2026-08-09).**
> (a) ~~the **consolidated cleanup round**~~ — **DONE 2026-08-09 (`9e85074`)**, full
> tower green (`MAKE_EXIT=0`, `BUG_EXIT=0`), wiring gate PASS, unsafe-check clean.
> Five definitions deleted: `B1-cSize≡sizeCapAt` (Caps-Bridge), `slotsGo?-widen` and
> `slotsCaps?-widen` (Caps-Face), `size≤budget` / `init-bounded` / `1≤sizeᵗˢ`
> (Measures). All were the `-core`'s scaffold for a route through `sizeBudgetAt`
> that #7's direct proof does not take; the stBounded?-at-init argument survives at
> the base cap inside `Init-Caps`. **`slotCaps?-widen` is NOT among them and was
> nearly swept with its two lexical neighbours** — it is live, consumed by
> `slotsCaps?-bound` (Caps-Face:913). A truncated grep hid the consumer. That is the
> THIRD time in this campaign a consumer sweep has been read past its output window
> (cf. `three-size-le-blowH`, twice, row 12): **when ruling on an orphan, read the
> grep to the end or widen it — a truncated consumer list is indistinguishable from
> an empty one.**
> (b) ~~the **P3 + #9 signature pass**~~ — **DONE 2026-08-09**, see the block
> above. It did NOT batch with (a): the pass is a large coherent unit and
> deserved its own commit and its own verification, so (a) still owes one
> full tower rebuild of its own.
> (c) `Demand-Battery.agda` was drafted (~520 lines, chainStep/foldPath demand rows
> aimed at the doubling live-seed shape) and DELETED unverified when the run was cut
> short — it never typechecked, and an unverified probe must not sit in `probe/`.
> Restart it from `SubInner-Demand-Probe.agda`'s method.

> **DELETION RECORD (2026-08-07, `1ef9b3d`).** `opIterD-budget-core`'s discharge
> orphaned its seven expression-level hypotheses' kit, and the sweep removed eight
> definitions: `entry-to-index`, `index-mono`, `entry-is-sweep` (Caps-Chain) and
> `residAt-connected`, `share-step-resid`, `mu-1≤k`, `mu-step-le`, `k-raise`
> (Caps-Nest). All were structural-route kit superseded by the pure level-arithmetic
> proof; `mu-step-le` was already recorded as superseded by `mu-step` at
> Subscribe-Face:3118. The predicted cascade to `resid-connect` / `resid-antitone`
> did NOT happen — both are still consumed (`share-step`, `nest-keeps`). Git is the
> archive.

### Tier 2 — the main proof branch (Verify-Well-Formed, 21; plus batch-online)

> **PARKED behind tier 1** — see THE TIER ORDERING LAW in the roadmap below.
> Tier 2 is built ON `budget-sufficient`, so proving anything here while tier 1's
> anchor question is open bets on ground a tier-1 design failure would move. The
> ranking is kept current; the WORK waits. Sole carve-out: merge-cert's
> STATEMENT (a design deliverable, not a proof).

| # | Postulate | Where | Class | Why it ranks here |
|---|-----------|-------|-------|-------------------|
| 1 | `burst-done-false` | VWF:1109 | **REFUTED 2026-08-06 — FALSE** | **Machine-refuted**, `agda/probe/Battery-Burst-Done.agda` (`burst-done-false-absurd`, a proven `→ ⊥`). `BurstInv`'s four fields never mention `done`, so `S = record { live = [] ; horizon = 0 ; current = nothing ; done = true }` inhabits it at `st-init`/`sched-init` and forces `true ≡ false`. Structural, hence shape-invariant over all `n`/`Γ`/`e`. **The source already knew**: VWF:876–882 says `done ≡ false` is a subscribe-TIME fact and "BurstInv cannot carry it; it must come from the walk order" — the postulate asserted what its own neighbour calls impossible. Repair is a SIGNATURE change, not a restatement — see Phase 2. |
| 2 | `root-done-plumbed` | VWF:1423 | FALSITY, blocked on merge-cert | The merge-coherence content. Candidate invariant #1 was machine-refuted by THREE counterexamples (VWF:3771–3800); route #2 is marked STRUCTURALLY DEAD (:3859); the corrected statement is OPEN (:3820–3858). Stated at the settled root exit — the one case the refutations do not touch — so plausibly true, but nobody knows the invariant that proves it. |
| 3 | `root-caches` | VWF:1438 | FALSITY, blocked on merge-cert | Same content, same blocker, same settled-state plausibility. Discharges together with #2. |
| 4–7 | `subscribeE-{merge,concat,switch,exhaust}All-wf` | VWF:1235–1268 | SHAPE | The four wrap-clause receipts, written against a merge-cert whose correct statement is UNKNOWN. Until it exists, the `valsLast?`/BurstInv conjuncts through a merge are conjecture — the statements may need hypotheses nobody has named yet. |
| 8 | `stepFrame-wf-outer` | VWF:4046 | SHAPE | The thru-outer wrap; same cluster, plus it inherits the FoldOut question. |
| 9 | `dispatchShare-wf` | VWF:4058 | **SHAPE — known too weak** | Its conclusion is only `Σ S′ → runProtocol … ≡ just S′` — no FoldInv/FoldOut carried out, so it CANNOT feed `mid-step` as stated (old W7 finding, still true). A guaranteed restatement, cascading into the stepFrame family. Wired, consumed, and wrong-shaped. |
| 10 | `mid-step-core` | VWF:4907 | FALSITY, moderate | Rests on `FoldOut` — a genuinely new 6-field invariant validated at exactly ONE clause (`foldPath-root-out`). If FoldOut's shape is wrong, this and the root proof both move. |
| 11 | `batch-online` | Batch-Theorems:12 | **REFUTED 2026-08-06 — FALSE** | Machine-refuted, `agda/probe/Battery-Batch-Online.agda` (`batch-online-refuted`, a proven `¬`). `impl-batchSimultaneous [em1,em2]` flushes an OPEN batch to `value [1]`, while on `[em1,em2,em3]` that batch closes as `value [1,2]` — the first elements differ, so no prefix relation holds. Exactly the failure its own `nb:` predicted. **Restatement drafted, NEEDS ANTHONY'S RULING** — see below. |
| 12 | `map-valsLast-push`, `scan-valsLast-push` | VWF:1124/1154 | SHAPE | Each papers over a recorded "REAL SHAPE MISMATCH" (the proven sub-lemmas don't return `valsLast?`). Plausible truths standing in for a missing conjunct in the proven work. |
| 13 | `map-nodry-push`, `scan-nodry-push`, `scan-nodeP` | VWF:1115–1141 | DIFFICULTY — **PROBED 2026-08-06** | `agda/probe/Battery-VWF-Prop.agda`: all three hold at concrete instances, non-vacuously (premise AND conclusion both live, not an empty-premise pass). `scan-nodeP`'s mechanism is that `ofᵉ` ignores its path argument and returns state unchanged, so the installed node survives at its seed. Coverage is ONE program each — thin, but the class is low-risk. |
| — | **`scan-binv-adapt`** | VWF:1168 | **DISCHARGEABLE — proof in hand** | Its comment was right: the proof is `record { live-matches = BurstInv.live-matches binv ; … }`, four fields passed straight through, verified in `agda/probe/Battery-VWF-Prop.agda`. It works because `installNode` touches only `nodes` and `mintNode` only `nextNode`, so `registry` and `live` are unchanged and record eta closes it with no rewrites. **Land it BUNDLED with the `burst-done-false` repair** — both edit VWF, and one ~40-min gate should carry both. |
| 14 | `subscribeE-input-wf-core`, `subscribeE-defer-wf`, `subscribeE-takeᵉ-wf-core` | VWF:1195/1218/1294 | DIFFICULTY | Per-clause receipts of the pattern already PROVEN three times over (map/scan/take clause proofs exist). Low statement risk. |
| 15 | `cut-owed` | VWF:4017 | DIFFICULTY, low | Self-contained Owed-table algebra, independent of every blocker. The easiest real proof in the branch. |
| 16 | `stepFrame-wf-inner-concat` | VWF:4037 | DIFFICULTY | concat's drain grows the registry; re-establish FoldInv. Independent of merge-cert. |

### Tier 3 — all the other theorems (~25)

> **PARKED behind tier 2** — see THE TIER ORDERING LAW. Bucket (b) is already
> probed, so there is nothing cheap left here anyway; bucket (a) needs Anthony to
> author definitions before it asserts anything at all.

Three buckets, in risk order:

**(a) VACUOUS BY ABSTRACTION — asserts ~nothing today; risk is reporting, not
falsity.** `Rx.Time-Theorems` entire: 9 abstract helpers (`Node`, `NodeSt`,
`Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`) under
`locality` / `non-interference` / `timing-invariance` — each claim is
satisfiable by trivial instantiation (`retime ρ = id` makes timing-invariance
free), so as stated they are close to vacuous, exactly as Main's CAUTION
records. Same class: `causality` (its `truncateIn`/`emittedBefore` are
postulated functions; `emittedBefore k = []` satisfies it), `μ-guarded` (its
type is IDENTICAL to `μ-unfold`'s — a duplicate asserting nothing new), and
`defer-shift` (`⊤` on purpose; the honest-gap exemption). **De-risking these
means DEFINING the abstractions — claim-authoring work that needs Anthony, not
a grind.** Until then they are parked, with the Main caution as the label.
NOTE for ledger readers: the wiring report shows `NodeSt`/`cascade` at
Rx/Evaluator.agda lines — that is the checker's known same-name merge
(Evaluator's REAL definitions colliding with Time-Theorems' abstractions), not
a postulate inside the evaluator.

**(b) REAL AND PROBEABLE — ALL PROBED 2026-08-06, no refutation found.**
`agda/probe/Battery-Eval-Laws.agda` and `agda/probe/Battery-Readme.agda`. The
first pass on both was DEGENERATE throughout and was rejected; the second pass
carries an explicit **LOAD-BEARING / DEGENERATE label on every row plus a
"what would make this fail" line** — that labelling is the reusable part, and
new rows here should keep it.

- **`μ-unfold`** — the one under real suspicion (`defer-shift`'s comment says
  unfolding re-mints ids, which would kill a strict `≡`). Now has genuinely
  self-referential rows: `μbody₁ = deferᵉ (varᵉ (here refl))` at fuel 1 and 2,
  where drain steps actually fire and the compared output lists carry the
  `init`/`close` events **with their instants**, so ids ARE part of the
  comparison. The suspected asymmetry — LHS budgeted at `budgetAt (μᵉ e)` vs RHS
  at `budgetAt (unfoldμ e)`, which could make one side hit `g0`/dryBurst while
  the other unfolds — is addressed directly: both sizes are ≥ 3, so both budgets
  carry ≥ 8 `gs` levels and the difference cannot decide either site.
  **RESIDUAL:** that last step is an ARGUMENT, not a proof, and coverage is
  `noSlots` with fuel ≤ 2. A program sized near the `gs`-level boundary is where
  it would break if it breaks.
- **`fuel-coherent`, `id-inheritance`** — probed; first-pass rows were
  degenerate (fuel that changed nothing; singleton ⊆ singleton) and were
  relabelled/extended.
- **The 10 `readme-*` claims** — every row classified. Two were DEGENERATE and
  are now backed by load-bearing siblings (`emptyᵉ` rows where `concat [] ≡ []`
  or `0 ≤ 1` passes regardless; `cascades-inherit` at `ws ≡ []` fired no cascade
  at all, so a new `ws ≡ [varᵗ (here refl)]` row was added). Each load-bearing
  row now names its failure mode — e.g. `readme-diamond` would fail with
  `(3∷[])∷(3∷[])∷[]` if the two paths fired at different instants, which is
  exactly the property the README is about. A refutation here is SPEC-level:
  surface to Anthony, do not patch.

**(c) FFI, zero proof risk.** `_>>=_`, `getContents`, `putStr` (CLI/IO),
`randFold`, `natMod` (QuickCheck) — GHC bindings for the two extracted
binaries, off every proof path. Carried, not counted.

### Where the risk actually is — the concentration facts

1. **Two design questions carry most of tiers 1–2:** THE ANCHOR PROBLEM
   (tier 1 ranks 1–3, 11) and MERGE-CERT (tier 2 ranks 2–8). Solving either
   moves a whole block; grinding around them moves nothing.
2. **Three postulates are suspected wrong by their own comments:**
   `burst-done-false` (SUSPECT: false as stated), `batch-online` (imprecise as
   stated), `dispatchShare-wf` (too weak as stated). Cheapest wins in the repo.
3. **A third of the ledger is machine-probeable today** and none of it has
   ever been probed. The QuickCheck/oracle harness only ever compared impl to
   spec; every postulate ABOUT the spec/evaluator is untested territory.

---

## THE ROADMAP

> ## THE TIER ORDERING LAW (Anthony, 2026-08-06)
>
> **TIER 1 IS FINISHED BEFORE ANY TIER 2 OR TIER 3 WORK RESUMES. STRICTLY.**
> Not "mostly", not "while we wait on a build" — tier 2 and tier 3 work
> *follows* tier 1 and does not interleave with it.
>
> **Why this is the right order, so nobody relaxes it for a plausible-sounding
> reason:** tier 1 (`Verify-Budget-Sufficient`) is what `budget-sufficient`
> rests on, and `evaluate-well-formed` — the whole of tier 2 — consumes
> `budget-sufficient`. So **tier 2 is built ON tier 1**. Every hour spent
> proving a tier-2 statement while tier 1's anchor question is open is an hour
> bet on ground that a tier-1 design failure would move. That is this
> campaign's most expensive class of mistake, and it has already been paid for
> once.
>
> **The one carve-out, and it is a DESIGN carve-out, not a grinding one:**
> answering a *design question* is cheap, is not the grind, and prevents the
> grind from being aimed wrongly. So MERGE-CERT's **statement** may land now
> even though its consumers are tier 2 — a statement is a one-line postulate
> plus a header, and having it settled costs nothing later. **What must NOT
> happen is the six rewrites and any tier-2 proof work built on it.** Those are
> parked behind tier 1 with everything else.
>
> **Practical test before starting any task:** if the postulate you are about
> to touch is NOT in the tier-1 table above, and the work is not one of the two
> design questions, it is parked. Say so and pick a tier-1 item instead.

Within tier 1, ordered so that each phase's findings can still cheaply change
the phases after it. Do not reorder: grinding before probing risks proving
towers over false ground.

### Phase 0 — THE FALSIFICATION SWEEP — ✅ COMPLETE (2026-08-06)

All seven targets resolved in one parallel sweep. Two REFUTED
(`burst-done-false`, `batch-online` — both had flagged themselves in comments),
two DISCHARGED (`scan-binv-adapt` landed; `three-size≤capsH-core` proven in one
line, landing pending), merge-cert SURVIVED its decisive reachability test,
`init-capsOK?-base` + `depth-compositional` probed with residuals recorded, and
`init-capsOK?` BLOCKED with its cause named. Detail per postulate is in the
ledger tables above. **The sweep's most valuable output was not a verdict but
the boxed CORRECTION on the caps axis: it is `abstract`-sealed and cannot be
probed at all**, which is why Phase 2 below is symbolic rather than numeric.

**THREE WAYS A PROBE LIES GREEN — all three observed on 2026-08-06's first
sweep, all three in the direction of false comfort. Check every probe report
against them before believing a PROBED-GREEN.**

1. **VACUOUS ROWS.** The rows pass because the quantifier is empty, not because
   the bound holds — `all _ [] = true`, `0 ≤ᵇ _`, a sweep over an empty list.
   `capsOK?` at `st-init` has THREE of five conjuncts vacuous by construction,
   so a green row there is evidence about nothing unless the shape was built to
   make the LIVE conjuncts do work. **Name the covered conjuncts, not the
   covered programs.**
2. **HAND-BUILT STATES.** A state written as `record (st-init e) { … }` is not
   a state the evaluator can reach, and a predicate checked only against states
   its own author invented is confirmation with the inputs chosen by the thing
   under test. **Reach states by RUNNING** (`evaluate` / subscribe / cascade);
   one reached row outweighs a table of constructed ones. Corollary: a
   constructed state where the predicate FAILS is not a "non-vacuity witness"
   to be noted and passed over — it is a refutation candidate, and its
   reachability is the finding.
3. **READING AN ASSEMBLY BACKWARDS.** `P = P-core o₁ … oₖ` proves **P from the
   postulated core**; it does NOT prove the core. The `oᵢ` are the core's
   HYPOTHESES. Mistaking this makes every `-core` in the repo look discharged —
   and every remaining tier-1 gap is a `-core`.

A fourth, from the same sweep: **a row that could not have failed is not a
row.** Label every probe row LOAD-BEARING or DEGENERATE and state what would
make it fail; the README and evaluator batteries carry the worked example.

### Phase 1 — THE TWO DESIGN QUESTIONS ← **YOU ARE HERE**

These are the campaign's real risk mass, and both are design work for the
design session, not worker grind.

- **1a. MERGE-CERT — SURVIVED (2026-08-06); land the STATEMENT only.**
  The corrected form has a computable shape, is seed-provable, and its
  reachability question is answered by the cascade ordering
  (`cascadeLatch` sets `dying` before any chain is processed; `cascadeGo` adds
  `rid` to `delivered` before `chainStep`; so `aliveThroughᶠ` is already false
  when `innerFinish` drops `k` to 0). Full detail and the uncovered residue are
  in the MERGE-CERT section below. **DO: state it in VWF with that mechanism in
  its header, citing the line numbers. DO NOT: rewrite the six consumers or
  prove anything over it — that is tier 2 and it is parked.**
- **1b. THE ANCHOR PROBLEM — the campaign's center, and now the critical path.**
  The 2026-08-06 probe round settled everything AROUND the anchor (see the
  section below), so this phase is no longer exploratory. It is four edits, in
  this order, and the order is the outside-in rule:

  1. **`Ŝ` ALREADY EXISTS — step 1 is FREE (found 2026-08-06, correcting this
     file).** The anchor is `sizeCapAt e sl (suc id)` (`Wet.agda:4109`,
     `= Caps.cSize (capsAt e sl id)`), a real definition, already threaded at
     the call site (`Caps-Bridge.agda:656`, `Ŝ = sizeCapAt e sl′ (suc id)`).
     `capsH e ins 0` was a PROBE CANDIDATE for a fresh anchor and is not
     needed — do not add a second one. Two facts already in hand come with it:
     `2≤sizeCapAt` (:4112) discharges `hop-edge`'s FIRST premise outright, and
     `sizeCapAt-mono` (:4118) lifts any bound at `id` to `suc id`.
  2. **STATE the dry family as POSTULATES** — `chainStep-dry` / `foldPath-dry` /
     `subscribeInner-dry`, each concluding that the observable reaching that
     site is `valB?`-bounded at the instant's own `B`. **The reachability source
     is `INV?`, and this is the round's second finding:** `INV? Ψ B sched st`
     already bounds every value the state holds by `B = sizeCapAt e sl id`
     (`valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)`,
     `Measures.agda:4875`). So `sizeᵛ o ≤ Ŝ` is NOT a fresh mystery — it is
     `valB?` at `id` composed with `sizeCapAt-mono`. **The whole remaining
     content is therefore ONE question: does the value ARRIVING at
     `subscribeInner` carry `valB?`, or is it freshly computed and outside
     `INV?`'s coverage?** That is what the three postulates assert, one per
     site, and it is the reachability induction in its smallest honest form.

     **DO NOT source it from the ledger.** `subscribeE-walk-core` concludes
     `burstB? (capᴱ W E′) Ψ …`, which looks like the bound wanted — but routing
     the anchor through `capᴱ W E′` is exactly the composition GAP 4 REFUTES
     (`walk-hyps-absurd`). The family sources from the CAPS face (`capsAt`,
     `caps-tick`), never from the receipt.

     ✅ **STATED AND GREEN, `02ffddc`** — `agda/probe/Anchor-Dry-Probe.agda`,
     three postulates plus `dry-hop`, the REAL (non-postulate) lemma closing
     `hop-edge`'s second premise from `valB?` and `sizeCapAt-mono`:
     `dry-hop B Ŝ Ψ o B≤Ŝ h = ≤-trans (valB-sz B Ψ _ o h) B≤Ŝ`. Telescopes
     match `Evaluator.agda:1592` / `:1542` / the `thruConsume` call sites
     (`:1109, 1121, 1130, 1140, 1196`). No `capᴱ` in any statement. Every
     hypothesis is caps-face (`INV?`, `capsOK?`, `valB?`, `pathB?`); every
     conclusion bounds the site's output at the FIXED `Ŝ = sizeCapAt e sl
     (suc id)` — fixed, so there is no Σ-witness to be upward-closed in.

     ⚠️ **THE RISK MOVED, IT DID NOT VANISH — AND THIS IS THE NEXT PROBE.**
     Each statement carries the growth of ONE INSTANT: inputs bounded at
     `B = sizeCapAt e sl id`, outputs at `Ŝ = sizeCapAt e sl (suc id)`, i.e.
     exactly one `frameBlowup` of headroom. But the adversarial doubling
     `scanᵉ` grows the accumulator by a FACTOR of ~2 per emission, and
     `syncSizeᵉ e` emissions can land in a single instant. So the headroom
     actually demanded is about `2^(syncSizeᵉ e)` — multiplicative in the
     emission count, not additive. `frameBlowup` is tower-shaped and very
     likely covers it, **but that is UNPROBED, and it is now the load-bearing
     arithmetic of the whole anchor.** If it fails, the three statements are
     FALSE as written and the repair is an anchor indexed by emission count
     within the instant rather than by instant alone. **Probe this BEFORE
     wiring the family into `subscribeE-wet-core`** — the wiring edit dirties
     `Wet.agda` (~14-18 min, plus everything above it), and grinding it over a
     false statement is the expensive mistake de-risk mode exists to prevent.

     ⚖️ **PROBED `f83186c` — HALF ESTABLISHED, AND THE OTHER HALF IS THE HALF
     THAT CARRIES THE RISK.** `agda/probe/Battery-Instant-Headroom.agda`
     (green) proves the CAPS side: `capsAt-covers-12pow`, i.e.
     `12 · 2^(sizeᵉ e + slotsSize sl) ≤ Caps.cSize (capsAt e sl id)` for any
     instant, over a proven chain (`capsAt-zero-size` by `refl`, `regAt-zero`
     via `*-identityʳ`, `i≤dWalkᶜ`, `J+n≤lvls`, `iterSize-le-capsAt`) plus two
     honestly-flagged postulates — `12·2^sz≤iterSize` (the real gap, verified
     by `refl` at sz = 1,2,3: `iterSize` = 129, 2340, 55555 against 24, 48, 96)
     and a trivial helper. Route 2 (numeric tables) is CONFIRMED DEAD:
     `sizeCount`, `cDel` and `blowH` are all `abstract`, so no numeral emerges
     from `sizeCapAt` — symbolic lower bounds are the only route, as the caps
     axis's `abstract` design already implied.

     **BUT THE COMPOSITION IS NOT PROVEN.** The growth is `12·2^k − 11` in the
     EMISSION COUNT `k`; the theorem bounds `12·2^sz` in the PROGRAM SIZE `sz`.
     Composing them needs **`k ≤ sz`**, and that step appears in the file only
     as prose (§6's "since max sizeᵛ ≤ 12·2^sz … see Battery-Obs-Growth"). It
     is exactly the repo's own lying-comment pattern: a qualification carrying
     the claim's weight, living where neither the typechecker nor `grep` can
     reach it. **It is also precisely the question the probe was sent to
     answer** — how many emissions land in ONE instant — so the receipt
     asserts its own open question as a premise.
     - **Half of the link is already proven and was not used**:
       `syncSize≤sizeᵉ` (`Measures.agda:698`), giving `syncSizeᵉ e ≤ sizeᵉ e`.
     - **The other half is measured but unstated**: `k ≤ syncSizeᵉ e`, i.e.
       emissions-per-instant is bounded by the sync measure. That is
       `Battery-Mu-Emissions`'s content, and it exists as measurements, not as
       a lemma. **State it, then the composition closes.**
     Until then this is a PARTIAL receipt: the caps ceiling is high enough for
     `12·2^sz`, and whether the growth stays under `12·2^sz` is still open.

     🔶 **`f04fb42` — THE GAP IS NOW NAMED RATHER THAN CLOSED, AND THE
     DISTINCTION MATTERS.** `obs-fits-headroom` typechecks the full chain
     `sizeᵉ o ≤ 12·2^k ≤ 12·2^(syncSizeᵉ e) ≤ 12·2^(sizeᵉ e) ≤ 12·2^sz ≤
     Caps.cSize (capsAt e sl id)`, correctly using the already-proven
     `syncSize≤sizeᵉ`. **But its hypothesis is UNINHABITABLE.** The step
     `k ≤ syncSizeᵉ e` was discharged by introducing
     `SyncCount : Closed Γ t → ℕ → Set` as a POSTULATED ABSTRACT PREDICATE
     with no definition and no introduction rule — so nothing in the repo can
     ever produce a `SyncCount e k` witness, `sync-count-bounded` is
     unfalsifiable (vacuously true if the family is empty), and the theorem
     cannot be instantiated at any program.
     - **This is CLAUDE.md's VACUOUS-BY-ABSTRACTION bucket** (Phase 5 (a)),
       arrived at from a new direction, and it is worth naming as a repeating
       failure mode: *an open step can be made to typecheck by promoting it to
       an undefined predicate, which looks like discharge and is not.*
     - **It IS progress, but only the wiring law's kind.** A prose
       qualification became a greppable, gated postulate — real, and preferred
       by the law. **The mathematical content is unchanged**, and the receipt
       must not be read as "the growth fits."
     - **THE REPAIR IS CONCRETE AND SHOULD NOT NEED A NEW ABSTRACTION.**
       `burstLen` (`Measures.agda:5654`) already counts emissions over the
       evaluator's REAL output stream, computably. State the bound over that —
       `burstLen (proj₁ (subscribeE …)) ≤ syncSizeᵉ e` at the right shape —
       and it becomes falsifiable, probeable by `refl` at concrete programs,
       and inhabitable at every call site. Delete `SyncCount` when it lands.

     ❌ **`2daa05b` — THAT REPAIR SHAPE IS REFUTED, AND THE ERROR WAS IN THE
     DIRECTIVE, NOT THE WORK.** `agda/probe/BurstLen-SyncSize-Probe.agda`
     (green, 7 `refl` checks) kills `burstLen (proj₁ (subscribeE …)) ≤
     syncSizeᵉ e` outright: at `deferᵉ emptyᵉ`, `burstLen ≡ 2` while
     `syncSizeᵉ ≡ 1`. `emptyᵉ` alone is worse (4 vs 1). Scan rows pass
     comfortably (5/6/7 against 14/15/16), so the failure is specific, not
     general.
     - **WHY IT FAILS — `burstLen` IS THE WRONG MEASURE.** It computes
       `sum (map (λ em → suc (length (InstEmit.events em))) b)`: one `suc` per
       `InstEmit` plus EVERY event, and `InstEvent` (`Rx/Prim.agda:107`) has
       `init`, `close`, `handoff` and `complete` beside `value`. The refuting
       burst carries one `init` and **zero `value` events** — so the number
       refuted is protocol bookkeeping, which a syntactic value-emission
       measure was never meant to bound. The mistake was naming `burstLen` in
       the directive; the probe did exactly the right thing with it.
     - **THE ANCHOR CLAIM IS UNTOUCHED.** Only `value` events feed a scan
       accumulator, so only they drive `12·2^k`. The measure needed is a
       VALUE-ONLY count over the same real stream — not yet defined anywhere,
       and a few lines to define.
     - **`SyncCount` correctly LEFT IN PLACE** for now: vacuous but not false,
       and deleting it before a correct replacement exists would strand
       `obs-fits-headroom`. Retire it when the value-count bound lands.
     - **STANDING LESSON, and it cost a round: name the measure by what it
       COUNTS, not by what it is called.** `burstLen` reads like "how many
       things did this burst emit" and is not that.

     🗼 **NESTING ESCALATES ONE EXPONENTIAL PER LEVEL — the per-instant
     headroom demanded is TOWER-shaped** (`agda/probe/Battery-Nesting-Escalation.agda`,
     green, all by `refl`). Two findings close steps 1–2 of the post-refutation
     plan:
     - **GAS IS NOT A COUNT BOUND, no run needed:** Battery-Value-Count's 30
       values ran on fuel of DEPTH 10. `subscribeInner` peels one `gs` per
       subscription and hands the same decremented fuel to every sibling —
       gas limits subscription DEPTH; breadth is free. The gas-sourced repair
       route is dead.
     - **THE ESCALATION LAW:** `nest src = mergeAllᵉ (scanᵉ step liveSeed src)`
       applies `v ↦ 2^(v+1) − 2` to the incoming per-instant count v — certified
       at v = 1..4 over `ofᵉ` sources and, the new fact, UNCHANGED at v = 2 when
       the source is itself a nested level (`nest²ᵃ ≡ 6`, instant 0). Composing
       from v = 1: 2, 6, 126, 2^127 − 2, … — a tower in nesting depth. Each level
       adds a CONSTANT to `sizeᵉ` while exponentiating the count, so **no fixed
       exponential in entry data bounds the per-instant count** — `12·2^sz`-class
       ceilings are dead for good, not just via `syncSizeᵉ`. (The v = 6 rows,
       predicted 126, exceeded a 10-min typecheck and are left uncertified in
       the file; coverage is honest there.)
     - **WHAT DECIDES THE DRY FAMILY NOW — step 3, the symbolic caps step.**
       (An earlier draft of this bullet said the cSize step "is one blowH
       application" — WRONG, that is the GAS height `capsHgo`. The real step,
       read off `capsAt-suc-full`: `Ŝ = iterSize B j B` with
       `j = sizeCount (capsAt e sl id) (capsH e sl id)`.)

     ⚖️ **STEP 3 DONE — THE RACE RESOLVES TO ONE NAMED INEQUALITY**
     (`agda/probe/Battery-Tick-Headroom.agda`, green). Proven, no postulates:
     `iterSize-doubles` (`sizeStep S s = S·(1+2s) ≥ 2s`, so one tick
     multiplies cSize by ≥ 2^j) and `headroom-arith` (`2^j·B` beats the
     instant's demand form `(2B+12)·towerℕ(suc sz)` as soon as
     `j ≥ 3 + towerℕ sz`, `sz = sizeᵉ e + slotsSize sl`). The assembly
     `tick-covers-instant` is a REAL definition typechecking against the
     actual `capsAt` recurrence.

     ✅ **`count-covers-tower` IS NOW PROVEN TOO — the headroom arithmetic
     is CLOSED, zero postulates in the file.** The recorded route executed
     as written: `fLvlD` is STRICTLY inflationary (`fLvl-pad` — both clauses
     factor through `fLvl + suc widAt`; the suc-d clause seeds `sIterD` with
     it via the existing `sIterD-zero≤`), so `iterL` advances by its budget
     (`iterL-plus`), `dLvl` climbs past `suc (sizeAt S J) + J` with
     `sizeAt S J ≥ 2^J`, hence `lvls 0 n` towers (`lvls-tower`, by induction
     with `pow2-mono`); and the count's budget `cDel ≥ cReg (capsAt) ≥
     2 + sz` (`dWalkᶜ-ge` — the walk visits `regAt S R 0 = R` positions,
     each adding ≥ 1 — plus `capsAt-reg`, cReg's base `suc sz` only ever
     multiplied up). Total: `sizeCount ≥ lvls 0 (2+sz) ≥ 3 + towerℕ sz`.
     **WIRING NOTE: `capsAt-reg` is the `capsAt-base-reg`-shaped sub-lemma
     tier-1 #8 names as its sole missing piece** (proven here at the
     stronger `2 + sz`); lift it into `Caps.agda` when #8 is picked up.
     **What remains open on the anchor is ONLY the demand model**
     (`a′ ≤ 2a + v + 11`, count ≤ towerℕ sz) — the dry family's own
       measured-not-proven content — that is what the
       three dry postulates assert.
  3. **TYPECHECK THE CONSUMER AGAINST THEM — ✅ DONE (2026-08-06), with one
     correction to this step's own wording.** The consumer is NOT
     `subscribeE-wet-core`: the dry family is `capsOK?`-conditioned and Wet
     deliberately reads NOTHING from the caps face (its own import comment),
     so the right layer is the caps↔wet bridge. Landed as:
     - `src/Verify-Budget-Sufficient/Tick-Headroom.agda` — the whole headroom
       chain, verbatim from the probe (deleted).
     - `src/Verify-Budget-Sufficient/Anchor-Dry.agda` — the dry family,
       FACTORED on landing: each dry statement is a real DEFINITION =
       demand postulate widened to `Ŝ` by `tick-covers-instant` (via
       `burstB?-widen`/`valsB?-widen`). The three `*-demand` postulates at
       the explicit form `(2·B + 12) · towerℕ (suc sz)` are now THE anchor's
       entire open surface, greppable.
     - `dry-tick-core` (Caps-Bridge) threads the family + `dry-hop` as four
       new hypotheses, supplied at `dry-tick` — the shape typechecks against
       the real recurrence; all four ledgered in DEFERRED.txt.
     If the demand form is wrong it now changes in one file, before any
     proof is ground over it.
  4. **THE UN-DEFERRING, ENFORCED IN `make wiring`** (Anthony, 2026-08-06) —
     ✅ **DONE, `bfa6b6e`.** `agda/DEFERRED.txt` holds 55 ledgered entries
     (≤152 →-slots); `make wiring-gate` ratchets against it. Verified by the
     design session, not merely reported: gate green at exit 0, and deleting
     `hop-edge`'s line fails it with the exact line to restore. `hop-edge`'s
     entry names the anchor premise as the worked example that motivated the
     ledger — so the debt this phase is about is now greppable from a file
     under version control. Design notes below are retained for the rationale.

  A third refutation here is still STOP-grade: it would mean tier 1's top three
  postulates have no surviving proof route.

  **THE UN-DEFERRING, AND WHY IT IS PART OF THIS PHASE.** Hoisting `sizeᵛ o ≤ Ŝ`
  out of `hop-edge`'s hypothesis position and into a named top-level postulate
  IS step 2 — the dry family and the un-deferring are the same edit seen from two
  sides. That makes this the right moment to close the hole that let the debt
  hide, because the fix and its first test case land together.

  **THE HOLE.** `make wiring` tracks NAMES, not OBLIGATIONS INSIDE TYPES. A
  proven lemma with unpaid premises, handed to a postulate as an argument, reads
  as fully wired: the name has a consumer, so no orphan, no gate failure — while
  its premises are never discharged by anything. That is how `hop-edge`'s size
  premise sat unexamined; the wiring law says every gap is a postulate with a
  real signature, and a premise buried in a hypothesis position is precisely a
  gap that is not.

  **THE FIX — promote (B4) from report to RATCHETED GATE.** (B4) already finds
  the passed-only lemmas (55 lemmas, ≤152 deferred →-slots at baseline). Make it
  bite:

  - **A checked-in ledger** (`agda/DEFERRED.txt` or equivalent) listing each
    passed-only lemma with the postulate that defers it. `make wiring-gate`
    EXITS 1 when the measured set is not the ledger's set.
  - **The ratchet runs one way.** A NEW passed-only lemma fails the gate until
    it is added to the ledger deliberately — so deferral becomes an explicit,
    reviewed act rather than a silent side effect of writing an assembly. A
    lemma LEAVING the set (its premises now discharged) requires deleting its
    ledger line, which is how the numbers come down and stay down.
  - **Ledger lines carry the reason**, one line each, naming what would have to
    exist to un-defer. Then "what debt is hidden in hypothesis positions?" is
    answered by a file under version control instead of by re-reading signatures.

  Baseline note for whoever lands it: (B4)'s →-slot count is an UPPER BOUND (it
  counts arrows, not distinct obligations), and it is textual — a lemma used only
  inside a `where` block can be misreported. The ledger inherits both caveats;
  record them in its header so the number is never read as exact.

### Phase 2 — TIER 1 STATEMENT REPAIRS + THE SYMBOLIC ATTACK

Tier-1 statements known to be wrong-shaped, and the caps axis's substitute for
probing. All of this is tier 1, so all of it precedes tier 2.

- ~~`sub-charge-capsOK-lift-core`~~ → **DONE 2026-08-06, better than repaired:
  the postulate is a real proof** (tier-1 row 4). The general form is the depOK
  premise; the one new gap is `sizeCount-mono-d` (tier-1 row 13).
- P4 `thruOuter-face-core` → resolve the "(a) may not fit `fCharge`" doubt at
  the statement level, per its own header.
- **`opIterD≤sizeCount-root-core` → DONE as a reduction (2026-08-06); the
  assembly is READY TO LAND into Caps-Bridge.** `agda/probe/Battery-OpIter-Symbolic.agda`
  holds it. Three things worth carrying forward:
  - **HOW TO REASON THROUGH THE SEAL — reusable for the whole caps axis.** All
    three `sizeCount-body` call sites use the same move: it is a `≤-reflexive`
    wrapper around an existing `lvls` inequality. So prove the `lvls` form, then
    wrap with `≤-reflexive (sym (sizeCount-body c d))`. That is the pattern for
    every sealed-symbol obligation here; do not re-derive it.
  - **THE NAIVE COUNT IS FALSE, and the reason fixes the shape.**
    `opIterD S W d k m 0 ≤ lvls S W d 0 m` — same count `m` on both sides — does
    NOT hold. Each `opIterD` suc-step sets `J₀ = suc (suc (S)²)` then applies
    `suc (widAt S W J₂)` passes of `fLvlD` where `widAt` grows as a TOWER
    (`foldStep S w = S^(suc w)`), while one `dLvl` step from 0 applies only
    `suc S` passes. So the count MUST be `cDel c d` (doubly exponential in `S`),
    which is what the postulate already says — its shape is right.
  - **THE REMAINING MATHEMATICS, named at last.** `opIterD-dominated` wants
    induction on `m` with a residual-budget invariant tracking `J` and remaining
    `D`, and the suc case needs a lemma of the form
    `fIterD S W d k n J ≤ lvls S W d J (‹bound in n›)` — dominating `fIterD`'s
    n-step application by some number of `dLvl` steps. **Finding ‹bound in n› is
    the open question**; that is the irreducible core of "the genuinely new
    mathematics", and it is now one inequality over ℕ rather than a statement
    about the evaluator.
- **Land `three-size≤capsH-core`'s discharge**, moving `three-size-le-blowH` and
  its helper chain from `Pool-Lower-Probe` into `Caps.agda`. **Decide the
  `S≤sizeStep` orphan in the SAME commit** — the discharge strands it (its only
  consumer is the assembly being replaced).
- **State `capsAt-base-reg`**, the one missing sub-lemma that lets proven
  `capsOK?-mono` lift `init-capsOK?-base` to `init-capsOK?` and retire the
  latter.

### Phase 3 — THE TIER 1 GRIND (workers; only over probed or repaired ground)

Cheapest-and-safest first, anchor-dependent mass last.

1. `three-size≤capsH-core` (proof in hand), `init-capsOK?-base-core` (proof
   sketch in hand from the two structural arguments) — the two tier-1 items
   closest to done.
2. `dry-tick-core`'s own bookkeeping, to whatever depth `cascadeGo-wet` allows.
3. P3 `innerFinish-concat-face-core` — real grind, no design blocker.
4. `depth-compositional` — LANDED in src as an assembly
   (Depth-Compositional.agda, 2026-08-06). The remaining work is its 11
   postulates, in this order: the 8 kit lemmas (burst-zero ×3,
   installNode ×2, size-arith ×3 — each mechanical, buckets (a)/(b)),
   then the 3 BUCKET-(d) blockers (`depth-conn-storeNest`,
   `depth-all-bound` — needs the storeNestMax-preservation conjunct
   proved simultaneously, census finding (4) — and `depth-μ-bound` via
   the guarded-context discipline).
4b. `sizeCount-mono-d` (tier-1 row 13) — the mutual d-monotonicity grind over
   the fLvlD SCC via its clause equations, mirroring `lvls-mono`. Mechanical
   once set up; the route is in the postulate's header. Worker-suitable.
5. The anchor cluster (`subscribeE-walk-core` → `subscribeE-wet-core` →
   `cascadeGo-wet-core` → `dry-tick-core`) — after 1b. This is the endgame and
   it stays LAST, because it is where a design failure costs the most reground
   work. **NEW STANDING OBLIGATION for this induction (from #4's discharge):
   the depOK PRESERVATION invariant.** `subscribeE-wet-via-caps` now carries
   the premise `depthE g b κ id now sched st ≤ capsH e sl id`; the root
   instance is discharged (`depthE≤capsH-root`), and the Phase-3 induction
   must carry it across instants. The mechanism is the recurrence itself:
   `capsH e sl (suc id) = blowH (capsH e sl id)`, and `blowH` is BY DESIGN
   "the worst one instant's cascades can do" — so the inductive step is a
   one-instant depth-growth bound (`depthE` data at `≤ h` grows to
   `≤ blowH h` in one instant), NOT `depth-capped` at the state's own caps
   (that route is off by `towerℕ` at every index — see row 4). This
   preservation lemma is genuinely new mathematics of the demand-walk flavor;
   it is NOT landed as a postulate yet because nothing consumes it until the
   induction exists (the wiring law), and it is recorded here so it is not
   lost.

**TIER 1 IS FINISHED when every postulate in the tier-1 table is discharged or
deleted.** That is the gate. Only then does the parked work below resume.

### Phase 4 — TIER 2, PARKED BEHIND TIER 1

Ready-to-go work deliberately NOT being done, so it is not lost:

- The six merge-cert consumers rewritten over 1a's statement
  (`subscribeE-{merge,concat,switch,exhaust}All-wf`, `root-done-plumbed`,
  `root-caches`, `stepFrame-wf-outer`).
- `dispatchShare-wf` → FoldOut-carrying conclusion (cascades into the stepFrame
  family signatures — change the signatures first, per the wiring law).
- `cut-owed`, `stepFrame-wf-inner-concat`, the per-clause WF receipts
  (`input-core`, `defer`, `takeᵉ-core`), `mid-step-core`'s FoldOut threading,
  and the two `valsLast-push` shape postulates.

### Phase 5 — TIER 3, PARKED BEHIND TIER 2

- Bucket (a) VACUOUS-BY-ABSTRACTION (all of `Rx.Time-Theorems`, `causality`,
  `μ-guarded`, `defer-shift`): de-risking these means **defining** the nine
  postulated abstractions, which is claim-authoring and needs Anthony. Flag,
  do not grind.
- Bucket (b) is PROBED (2026-08-06) with residuals recorded; proofs are Phase 5.
- Bucket (c) FFI is permanently trusted, not counted.


---

## THE ANCHOR PROBLEM — the campaign's one central open question

`hop-edge` (and `connect-edge`) reset their demand to an anchor `Ŝ`, and
discharging one requires `sizeᵛ o ≤ Ŝ` for a value `o` arising **mid-walk /
mid-cascade**. There are exactly two ways to source `Ŝ`, and **the repo has
already proven both impossible**:

- **A fixed, entry-computable cap** — refuted by `caps-frame-boundary-absurd`
  (`Caps-Face.agda`, proven): for any cap `C ≥ 1`, `sizeStep C C ≤ C → ⊥`.
  One more frame-crossing always escapes the cap, *uniformly in the cap*.
- **A ledger/walk-position-tied ceiling** — refuted by
  `round3b-ledger-reset-absurd` (`Measures.agda`, proven): tying the anchor
  to the walk's own growing ceiling is circular.

The one surviving option is the repo's own stated plan — source `Ŝ`, `R̂`, `F`
from **reachability** (`Measures.agda:6199-6203`) — and it **is not established
anywhere.** No `chainStep-dry`/`foldPath-dry`/`subscribeInner-dry` family
exists, and every proven `-wet` delivery lemma is size-axis only — none carries
a `Gas` hypothesis or concludes `hasDry ≡ false`.

> ### ANCHOR STATUS AFTER 2026-08-06's PROBE ROUND — THE ROUTE IS ALIVE AND NARROWED TO ONE LEMMA
>
> Four probes ran against the surviving reachability route. **None refuted it, three
> retired a way it could have died, and the surrounding constraints are now verified
> satisfiable.** What remains is a single obligation.
>
> **1. The μ ESCAPE IS BLOCKED BY TYPING — so the emission count is entry-bounded.**
> (`agda/probe/Battery-Mu-Emissions.agda`.) `μᵉ` binds into the GUARDED context `Δᵍ`
> while `varᵉ` reads from `Δ`, and `deferᵉ` is the sole gate between them — so
> `μᵉ (varᵉ (here refl))` is a TYPE ERROR and synchronous self-subscription is not
> writable. Measured contrast across an unfold: `sizeᵉ` DOUBLES (10 → 20) while
> **`syncSizeᵉ` is STABLE (9 → 9)**. The load-bearing fact, now named:
> `syncSize-μ-invariant : syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body`.
>
> > ❌ **REFUTED 2026-08-06 — "per tick, emissions ≤ `syncSizeᵉ e`" IS FALSE, and
> > it was the cornerstone claim of this section.** `agda/probe/Battery-Value-Count.agda`
> > (green, every row by `refl`) measures VALUE emissions in ONE instant against
> > `syncSizeᵉ`, on a doubling `scanᵉ` over a **live** seed:
> >
> > | K | valueCount | `syncSizeᵉ` | holds? |
> > |---|---|---|---|
> > | 1 | 2  | 17 | ✓ |
> > | 2 | 6  | 18 | ✓ |
> > | 3 | 14 | 19 | ✓ |
> > | 4 | **30** | **20** | **✗ REFUTES** |
> >
> > `valueCount = 2^(K+1) − 2` (exponential in source length) against
> > `syncSizeᵉ = 16 + K` (linear); they cross at K = 4 and the gap widens.
> > `maxInstant ≡ 0` on the refuting burst, so this is genuinely PER-INSTANT.
> > **The mechanism:** `syncSizeᵉ (mergeAllᵉ e) = suc (syncSizeᵉ e)`
> > (`Exp.agda:509`) charges a bare `suc` for a merge, while a merge over a
> > doubling accumulator subscribes an exponentially large tree of live leaves
> > inside the one instant. A syntactic measure charging additively cannot bound
> > a multiplicative runtime effect.
> > **Why it was believed:** `Battery-Obs-Growth`'s scan uses `seed = strmᵗ emptyᵉ`,
> > so every accumulator is a tree of merges over EMPTY leaves — it grows in SIZE
> > while emitting nothing. Changing one token (`emptyᵉ` → `ofᵉ [0]`) makes the
> > leaves live and the counts explode. **A near-miss shape can look like a
> > covering shape; this one hid the refutation for four probe rounds.**
> > **What it kills:** every anchor route through emissions-bounded-by-syntax,
> > including `sync-count-bounded` in `Battery-Instant-Headroom.agda` (FALSE the
> > moment its abstract `SyncCount` is instantiated to the real count) and the
> > chain `sizeᵛ o ≤ 12·2^k ≤ 12·2^(syncSizeᵉ e)` built on it. Since `k` is
> > itself exponential in program size, **`sizeᵛ o` is DOUBLY exponential in
> > entry data — not `12·2^sz`** — so `capsAt-covers-12pow` is the wrong ceiling.
> > **What it does NOT kill:** the three dry postulates bound `sizeᵛ` at
> > `sizeCapAt e sl (suc id)`, which is tower-shaped and may still dominate a
> > doubly-exponential value. **That is the open question now, and it is a
> > different one.** The μ typing fact itself (`deferᵉ` gates `Δᵍ`→`Δ`) stands;
> > what falls is the inference from it to a syntactic emission bound.
>
> **2. BOTH CEILINGS FIT** (`agda/probe/Battery-Anchor-Fit.agda`), against the
> candidate `Ŝ-cand e ins = 12 · 2^(sizeᵉ e + slotsSize ins)`:
> - `Ŝ ≤ capsH e ins 0` — FITS, with one arithmetic gap `exp12≤blowH` (route:
>   `blowH m ≥ 2·poolCount (towerℕ m) m ≥ 2·towerℕ m ≥ 12·2^X` when `m ≥ 4 + X`,
>   via Pool-Lower-Probe's `capsBase-le-pool`).
> - **`dBound` at that `Ŝ` fits under `budgetAt e ins 0` — FULLY DERIVABLE, no new
>   postulates.** This was the failure mode most worth fearing: an anchor big enough
>   to bound the values could have blown the walk's own budget, killing the route
>   *even if the size bound were true*. It does not. The chain mirrors
>   `caps-fuel-root` in Wet.agda exactly.
>
> **3. THE LARGEST WORKABLE ANCHOR IS `capsH e ins 0` ITSELF** — ceiling 1 holds at
> equality and ceiling 2 by the same chain. **So `Ŝ` need not be a bespoke
> exponential; take `Ŝ := capsH e ins 0`** and both ceilings come for free. That is
> the design ruling this round buys.
>
> **4. HOP-EDGE'S THIRD PREMISE discharges from an existing walk conjunct** (below).
>
> **5. THE GROWTH RATE IS CAPPED AT EXPONENTIAL — the shape of `Ŝ` is settled**
> (`agda/probe/Battery-Reached-Sizes.agda`). Sizes REACHED through the evaluator's
> real `scanVals` path (Evaluator:1052–1056), which is what `thruWalk` hands to
> `subscribeInner`:
>
> | k | `sizeᵉ progₖ` | max `sizeᵛ` at `subscribeInner` |
> |---|---|---|
> | 1 | 15 | 13 |
> | 2 | 16 | 37 |
> | 3 | 17 | 85 |
> | 4 | 18 | 181 |
>
> Program size grows LINEARLY (+1 per source element); the observable grows
> EXPONENTIALLY. **A linear anchor is refuted by this table.** A tripling step was
> also built (`Aₖ₊₁ = 3·Aₖ + 15`, giving `1, 18, 69, 222`) — so the base is
> tunable. **But super-exponential is IMPOSSIBLE for a fixed step function:** an
> `Fn` of size `S` with branching factor `n` (occurrences of the accumulator in
> its output) yields `sizeᵛ accₖ = O(nᵏ)`, and `n ≤ S ≤ sizeᵉ e`. Growing `n` with
> `k` would take a non-fixed `Fn`, which is not writable. **So `Ŝ` is exponential
> with an entry-bounded base AND an entry-bounded exponent** (`k ≤ syncSizeᵉ e`
> per §1) — comfortably under `capsH`'s tower.
>
> **6. `connect-edge`'s BOUND IS FREE — only `hop-edge` is hard.** `slotSize
> (shared d) ≡ sizeᵉ d` (Slots.agda:61), so `sizeᵉ d ≤ slotsSize ins < capsBase
> e ins ≤ Ŝ`. Shared defs are fixed at program entry and cannot grow at runtime.
> That retires one of the two anchor edges outright.
>
> **WHAT REMAINS — one lemma, and it now looks PROVABLE.** Prove `sizeᵛ o ≤ Ŝ` for
> every observable `o` REACHABLE at `subscribeInner`. Everything around it is
> settled: the ceilings fit, `Ŝ := capsH` works, the descent premise discharges,
> `connect-edge` is free, emissions are entry-bounded, and growth is at most
> `O(nᵏ)` with both `n` and `k` entry-bounded. **The remaining content is the
> REACHABILITY INDUCTION** — that every `o` arriving at `subscribeInner` is
> produced by at most `k` applications of a fixed step function to entry syntax.
> That is what the dry family (`chainStep-dry` / `foldPath-dry` /
> `subscribeInner-dry`) has to say.

**WHAT THE DELIVERABLE ACTUALLY IS — it is CODE, not an argument.** `hop-edge`
and `connect-edge` are already PROVEN and already wired in as hypotheses of
`subscribeE-wet-core` (Wet.agda:4344, :4350). Nothing is missing from the descent
machinery. What is missing is the ability to discharge their PREMISES at the call
site, and that takes exactly ONE artifact — **the dry lemma family**
(`chainStep-dry` / `foldPath-dry` / `subscribeInner-dry`) proving the premises
for every `o` that actually reaches `subscribeInner`. **`Ŝ` itself is NOT
missing** (corrected 2026-08-06): it is `sizeCapAt e sl (suc id)`, defined at
`Wet.agda:4109` and already threaded at `Caps-Bridge.agda:656`. An earlier
reading of this file called for defining it; that would have added a second,
competing anchor. Discharging them unblocks tier 1 ranks 1, 2, 3 and 11 together.
Per the outside-in rule, (1) lands as a real definition and (2) as postulates
FIRST, with `subscribeE-wet-core`'s proof typechecking against them — so a wrong
`Ŝ` changes in one place instead of invalidating finished work.

**And (2) IS the un-deferring.** Stating the family hoists `sizeᵛ o ≤ Ŝ` out of
`hop-edge`'s hypothesis position — where `make wiring` cannot see it — into a
named postulate it can. Phase 1b step 4 makes that permanent by ratcheting (B4);
see the phase entry above.

**HOP-EDGE'S THIRD PREMISE — RESOLVED 2026-08-06, and it is NOT a second design
blocker.** `hop-edge`'s signature is `2 ≤ Ŝ → sizeᵛ (obs u) o ≤ Ŝ →
hopDᵛ Ŝ (obs u) o < r → …`. The campaign's anchor discussion is entirely about
the second premise, so the third — the DESCENT condition — was checked
(`agda/probe/Battery-Hop-Premise.agda`, green). It discharges in two lines from
material that already exists:

- at the `*All` frame, `r` IS `hopDᵉ Ŝ (mergeAllᵉ b) = suc (hopDᵉ Ŝ b)` —
  definitional, `Rx/Hop-Depth.agda:191`;
- `subscribeE-walk-core`'s conclusion already carries the conjunct
  `burstHopD? F (hopDᵉ F b) burst ≡ true` (Measures.agda:5810), labelled in
  source as "the hop edge's feed, at the index the child also reads", giving
  `hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b`;
- so `hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b < suc (hopDᵉ Ŝ b) = r`. Wet.agda:4046 said as much
  all along ("the r-drop is the emitted-value invariant (burstHopD?)").

**It is not free, though — it is ABSORBED into `subscribeE-walk-core`.** The
`burstHopD?` conjunct is part of that postulate's conclusion, so proving the walk
must prove it too. Classed DIFFICULTY, not FALSITY: its engine is proven
(`hopD-applyFn`, Measures:2765) as is its mapᵉ consumer (`hopD-map-emit`, :2780).

**The two premises share a failure mode**, which is the useful reduction: on the
adversarial doubling scan, `hopDᵉ V accₖ ≡ k` (LINEAR) while the parent
`hopDᵉ V (mergeAllᵉ (scanᵉ …)) ≡ suc (3^V)` (exponential in `V`) — at `V ≡ 4`,
`3` against `82`. So (iii) can only fail where (ii) already fails. **The anchor
problem remains the single design gate.**

**`connect-edge` has NO analog** — its descent energy comes from `U` dropping
strictly via `unconn-insert`, while `r`/`s` merely RESET (`reach-reset`), needing
no strictness. Its sole open obligation is the same anchor question,
`sizeᵉ d ≤ Ŝ` for a slot def.

**CORRECTION, and the standing lesson landing on this file itself:** the note this
replaces said the third premise "appears nowhere and has never been examined."
That was true of PROOF-STATE and FALSE of the repo —
`agda/probe/Hop-Descent-Probe.agda:202–230` was built for exactly this obligation
and measured it on three shapes. What today added is the adversarial `scanᵉ`
shape, which that probe explicitly did not cover ("no scanᵉ in any witness"). Grep
the repo before declaring a gap, including when the gap looks new.

**NEW CONSTRAINT ON `Ŝ`'s SHAPE (2026-08-06, machine-checked):
`Ŝ` CANNOT BE LINEAR IN `sizeᵉ e`.** `agda/probe/Battery-Obs-Growth.agda`
establishes, by `refl`:

- **`scanᵉ` carries NO `isData` restriction on its accumulator type** (Exp.agda:67;
  the guard exists only on `scripted` slots, Slots.agda:40, and
  `isData (obs _) ≡ false`). So the accumulator may be `obs u`-typed, and
  `strmᵗ` (Exp.agda:96) lets the step function return an observable built from
  its own input. The doubling step
  `strmᵗ (mergeAllᵉ (ofᵉ (acc ∷ acc ∷ [])))` typechecks with nothing to stop it.
- **Inner observable sizes then grow exponentially in the emission count**, on
  the recurrence `sizeᵛ accₖ = 11 + 2 · sizeᵛ accₖ₋₁`, closed form `12·2ᵏ − 11`:
  measured `1, 13, 37, 85` at `k = 0…3`.
- **The killer number: `sizeᵉ prog₃ ≡ 17` while its own max inner is `85`.** A
  17-symbol program reaches an inner observable 5× its own size, so any anchor
  derived LINEARLY from program size is refuted outright. `Ŝ` must be at least
  exponential in entry data.

**WHAT THIS DOES NOT ESTABLISH — the route is NOT dead.** The probe's source is
`ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])`, i.e. `k ≡ 3` is SYNTAX. A scripted slot's
values live in `ins`, which is entry data too, so `k ≤ slotsSize ins` and
`Ŝ ≈ 12·2ᵏ` stays entry-computable — merely exponential, not unbounded. And
`capsH = blowH (capsBase e ins)` is a TOWER in `m`, which dominates `12·2ᵐ`
comfortably. A first pass claimed the route dies for scripted sources via
`Ŝ > capsH`; that ASSUMED `Ŝ > capsH` rather than deriving it, and the refuting
program was never built.

**SO THE ANCHOR QUESTION IS NOW SHARPER, AND THIS IS ITS DECIDING FORM:**

> Can the number of emissions into a doubling `scanᵉ` within ONE anchor scope
> (one subscribe walk, or one cascade) exceed anything computable from `e` and
> `ins`?

The only generator that could do it is `μᵉ` — and **the standing sync-μ ruling is
what likely saves the route**: `deferᵉ` is the sole gate moving `Δᵍ` into `Δ`, so
a μ's self-reference costs a TICK and synchronous self-subscription is not
writable (see the ruling below). If that holds, per-instant emissions are
syntax-bounded, `Ŝ` is entry-computable-exponential, and it fits under the tower.
**Then the sync-μ ruling is not a side note — it is the load-bearing fact of the
anchor proof**, and should be cited as such wherever `Ŝ` is sourced.

**This unifies what looked like separate problems.** GAP 4(b), `dry-tick`, and
P1's subscribe side are the SAME question on different axes: *can a mid-walk
value's size be bounded from reachability, rather than from a fixed cap or from
the ledger?* Answer it and tier 1's top block falls together; leave it and none
of it moves.

**Σ-receipt caution, standing:** `walk-hyps-round3b` (Measures) is a proven
receipt showing the edge constraints are jointly satisfiable at ONE entry
point. Per CLAUDE.md's Σ-receipt rule that is not an end-to-end induction, and
its own comment says so. Do not read it as "the walk is basically done."

## MERGE-CERT — the well-formedness branch's own anchor-shaped blocker

Blocks the `*All` wrap receipts, `root-done-plumbed`, `root-caches`,
`stepFrame-wf-outer`. Candidate invariant #1
(`merge-st k at nid ⇒ k ≡ countRegsUnder nid registry`) is **machine-refuted by
three independent counterexamples** (VWF:3771–3800 — the outer's own
`thru-outer` threads nid; a multi-source inner registers two chains under one
`bump`; `finish mergeᵒ` decrements `k` without dropping the registry). The
"derive from `Inv.done-plumbed`" route is **STRUCTURALLY DEAD** (VWF:3859 — its
premise is vacuous exactly when the obligation is needed). The corrected route
is identified but OPEN (VWF:3820–3858): one-directional and liveness-aware,

```
merge-cert : (merge-st k _ at nid) ⇒ k ≡ 0 ⇒ no aliveThrough inner
             INSTANCE under nid survives
```

keyed on the `from-inner allNid ≡ nid` frame only (dodges refutation 1), deduped
by `inst` (dodges 2), and excluding spent registrations (dodges 3). **Do not
generalise it to a global node↔registry theory, and not onto `dispatchShare`**
(standing, VWF:3800).

**PHASE 1a RESULT (2026-08-06): SURVIVES THE DECISIVE TEST — STATE IT AND
UNBLOCK THE SIX.** `agda/probe/Battery-Merge-Cert.agda` gives merge-cert a
computable form (`mergeCertAt`, over `innerInstsP` + `aliveThroughᶠ`), and
`k ≡ 0 ⇒ none` **IS seed-provable** (`merge-st 0`, empty registry, by `refl`).

**THE MECHANISM — this is the real deliverable, more than any row.** The probe's
own Shape B (`merge-st 0` with a from-inner registration where `dying`,
`delivered`, `cancelled` are all empty) is a state where merge-cert is FALSE, so
the whole question was its REACHABILITY — exactly where refutation R3 pointed.
The cascade ordering answers it:

- `cascadeLatch` (Evaluator:1617–1622) fires FIRST, setting `dying = [arrSource a]`
  **before any chain is processed**;
- `cascadeGo` (Evaluator:1633–1641) adds `rid` to `delivered` **before** calling
  `chainStep`;
- so by the time `innerFinish` decrements `k` to 0, `src ∈ dying` AND
  `rid ∈ delivered` both hold, making `aliveThroughᶠ ≡ false` for the spent
  registration.

The "both" is load-bearing — `aliveThroughᶠ` stays TRUE if only one holds — and
the ordering supplies both. **Shape B is unreachable by this path.**

**REACHED rows** (not constructed — the earlier pass's rows were all hand-built
and are retained only as a behaviour table): `mergeAll(of([slot0]))`, slot 0 hot
at tick 1, driven through `subscribeE` → `cascadeLatch` → `cascadeGo`. Mid-cascade
(`merge-st 0`, reg still in the registry, `dying=[0]`, `delivered=[0]`) → `true`;
post-`cascadeFinish` → `true`. The mid-cascade row is the decisive one.

**STILL UNCOVERED, and worth stating before anyone over-reads this:** ONE program
was reached, the R1/R3 shape. **R2 (multi-source inner) is covered only at
hand-built states**, as are concat/switch/exhaust and nested `*All`. And the
ordering argument covers the *cascade* route to `k ≡ 0` — **the CUT route is
untested**, though R3's own note says registrations are dropped "only at
cut/cascadeFinish", so a take-cut reaching `k ≡ 0` is a distinct path.

**FoldOut, the second statement-level debt in this branch:** a genuinely new
invariant (what a PARTIAL chain fold preserves of the live↔registry shadow),
stated as a 6-field record and validated at exactly one clause
(`foldPath-root-out`). `mid-step-core` consumes it; `foldPath-wf`'s signature
does not yet thread it, and restating W5/W6/W7 over it is Phase 2 work.

---

## Standing rulings (each one prevents a specific dead route — keep)

**RULING: `depth-capped` must be spent at the SMALL caps `c₀`
(`baseCaps e ins`), never at `capsAt e ins 0`.** The blown-up caps' `cSize` is
`sizeStep` iterated `sizeCount`-many times, and closing the gap to `capsH`
demands a cross-`M` growth-rate argument that exists nowhere in the repo;
`capsAt-tower` points the wrong way. At the root, three of `capsOK?`'s five
conjuncts are vacuous on the empty initial state and the two live ones are
syntax-ceiling-shaped — which is what `c₀`'s fields ARE. Full reasoning in
`Caps-Bridge.agda` above `init-capsOK?-base-core`; arithmetic chain rehearsed
in `agda/probe/Pool-Lower-Probe.agda`. **The unverified premise — the two live
conjuncts actually holding at c₀ — is Phase 0c / task #19.** If either fails,
c₀ grows and the arithmetic re-runs at whatever it grows to.

**Depth obligation must be conditioned.** Unconditional `depthE ≤ capsBase` is
FALSE (machine-refuted, `agda/probe/Depth-Blowup-Probe.agda`), and
unconditional `depthE ≤ capsH` is indefensible against adversarial stored
state. The honest statement conditions on `capsOK?` — already in scope at every
consumer.

**Fold-threading (standing).** P2 does not decompose into a per-chainStep
contract at fixed bounds (`caps-frame-boundary-absurd`). The honest
decomposition threads per-cascade growth, which the caps face's `j` index does
and any eventual `chainStep-wet` must mirror.

**Sync-μ escape: CLOSED BY TYPING.** `deferᵉ` is the sole gate moving `Δᵍ`
into `Δ`, so a μ's self-reference costs a tick; synchronous self-subscription
is not writable. Recorded at Wet.agda:4186 and Caps-Face:6087. Do not
re-refute this.

**THE GAS AXIS IS PROVEN AND WIRED.** Exactly three decrement edges (μ unfold,
share connect, inner-value subscribe — enumerated against every clause of the
subscribe clique), all three packaged and proven in Wet ("THE THREE GAS EDGES,
PACKAGED"), now consumed as `subscribeE-wet-core` hypotheses. Zero corners are
vacuous, not holes. What is NOT proven is SPENDING the edges mid-walk — that is
the anchor problem, not a gas gap.

**Ψ-only faces cross the ledger gap today** (`fn-tick`'s template): a
conclusion that does not read the numeric bound can reuse `cascadeGo-walk`
directly. Worth trying face-by-face before assuming the anchor blocks one.

**MAIN IS THE TOP-LINE PROOF.** Whatever Main imports sticks around; Main
names individual definitions, never a bare `open import`; Main is never touched
without Anthony's explicit approval. `make wiring` roots its exempt set there.

**The standing lesson.** This campaign's dominant failure mode is not wrong
proofs — it is not knowing what it already has. Grep for a fact before planning
its proof; grep for a lemma's consumers before believing any status written
here — including in this file.

## PROBE ROADMAP TIES — every survivor has a named deletion trigger

**22 files, and not one of them is kept "in case".** Each is tied to a roadmap
item, and each carries its own `-- ROADMAP:` / `-- DELETE WHEN:` header naming
the same tie. **The duplication is deliberate cross-checking: if you change one,
change the other.** A probe whose trigger has fired and which is still on disk is
a bug in this table, not a judgement call — delete it.

The tie exists because "when does this go?" was previously answered per-session
from scratch, which is how 60 files accumulated. It is answered here once.

**The eight triggers:**

| id | DELETE the tied probes WHEN … |
|---|---|
| **T1** | ~~`subscribeInner-Ψ` and `wet-thru` (.Burst-Walk § 2.3) and `subscribeInner-demand` (.Anchor-Dry) are discharged~~ **MILESTONE REACHED 2026-08-10**: all three are real definitions; the two new subscribeE-level postulates (`subscribeE-Ψ`, `subscribeE-demand`) name the subscribe-side burst face — same gap as `subscribeE-walk-core` |
| **T2** | `subscribeE-walk-core` is discharged (tier-1 #1) |
| **T3** | tier-1 #5's remaining depth postulates are discharged |
| **T4** | `merge-cert` is stated in src AND discharged (task #33) |
| **T5** | the five VWF push postulates are discharged |
| **T6** | `μ-unfold` / `fuel-coherent` / `id-inheritance` are discharged |
| **T7** | `The-Proof.agda` is discharged — a dead route cannot be retried once the proof is done |
| **T8** | its last dependent probe is deleted |

**The ties:**

| probe | roadmap item | trigger |
|---|---|---|
| `Battery-Nesting-Escalation` | tier-1 #1/#2/#3 — measured basis of `demand` (Anchor-Dry:28) | T1 |
| `Battery-Obs-Growth` | tier-1 #1/#2/#3 — source of Anchor-Dry:27's `a′ ≤ 2a+v+11` | T1 |
| `Battery-Reached-Sizes` | tier-1 #1/#2/#3 — establishes `Ŝ := capsH e ins 0` | T1 |
| `Battery-Value-Count` | tier-1 #1/#2/#3 — REFUTES `sync-count-bounded` | T1 |
| `Battery-Mu-Emissions` | tier-1 #1/#2/#3 — the μ leg of the composition | T1 |
| `SubInner-Demand-Probe` | tier-1 #3 — `subscribeInner-demand`'s only coverage | T1 |
| `Walk-Core-Census-Probe` | tier-1 #1 — per-clause sub-postulate census for `subscribeE-walk-core` | T2 |
| `Battery-Hop-Premise` | tier-1 #1 — how `hop-edge` premise (iii) discharges | T2 |
| `Cascade-Go-Wet-Core-Probe` | tier-1 #2 — `cascadeGo-wet-core` falsity probe (PROBED-GREEN 2026-08-11; NOT COVERED: from-inner/thru-outer paths) | T2 |
| `Install-Scan-Depth-Probe` | tier-1 #5 — `installScan-depth-bound` | T3 |
| `Depth-Wire-Probe` | tier-1 #5 — `baseCaps-is-inner`, parked outside the graph by design (Caps-Bridge:1018) | T3 |
| `Battery-Merge-Cert` | TIER 2, task #33 — the corrected `merge-cert` | T4 |
| `Battery-VWF-Prop` | TIER 2 — the five VWF push postulates (VWF:1119-1163) | T5 |
| `Battery-Eval-Laws` | Rx laws — `μ-unfold`, `fuel-coherent`, `id-inheritance` | T6 |
| `Nest-Budget-Probe` | ROUTE GUARD — `nestᵉ` is the wrong measure (Caps-Face:6294) | T7 |
| `Nest-Count-Probe` | ROUTE GUARD — per-instant width-count is false (Caps-Face:6299) | T7 |
| `Level-Walk-Probe` | ROUTE GUARD — `old-cDel≤new-cDel` justifies the live `cDel` (Evaluator:505,572) | T7 |
| `Joint-Probe` | ROUTE GUARD — joint bound false, so `subscribeE-caps` recurses at `suc j` | T7 |
| `Instant-Height-Probe` | ROUTE GUARD — store-growth rows the caps tower must keep dominating | T7 |
| `Charge-Probe` | INFRASTRUCTURE — program families for 4 probes | T8 |
| `Mint-Loop-Shapes` | INFRASTRUCTURE — measurement harness for 6 probes | T8 |
| `Instant-Height-Main` | INFRASTRUCTURE — GHC driver for Instant-Height-Probe | T8 |
| `Nest-Count-Main` | INFRASTRUCTURE — GHC driver for Nest-Count-Probe | T8 |
| `Measure-Main` | INFRASTRUCTURE — GHC driver for Mint-Loop-Shapes | T8 |

**Why T7 is not "keep forever".** A route-guard's job is to stop a refuted
approach from being retried while the proof is still being written. Once
`The-Proof.agda` is discharged there is nothing left to retry, and the guard's
content survives where it already lives: the src comment that states the
finding with its numbers. Every T7 file above was checked to have such a
comment — that is the precondition for the tie, not an assumption.

**T8 is mechanical and has a gate.** `make wiring-gate` § C3 fails on a probe
importing a module that no longer exists, so an infrastructure file deleted
early fails loudly instead of silently breaking its dependents.

**One survivor cannot be verified by the compile rule:** `Joint-Probe` does not
typecheck against `agda/src` BY DESIGN — it builds only inside the instrumented
scratch project `scripts/joint-probe.sh` creates. Its ledger line says so. It is
the one file where "it compiles" is not the acceptance test.

## Debts on next touch (cheap, fold into a pass that dirties the file anyway)

- **Prose that outlived its code:** eight comment references to `measureE` and
  two to `rank-lt-pow` survive in Keeps-Ring (:149,179,267,332,404),
  Wet (:2211,:2273), Rx/Slots (:32), Rx/Hop-Depth (:4), Measures (:1866).
  Keep the reasoning, mark the names retired. Not worth a solo ~45-min rebuild.
- **Two lying comments:** Caps-Face:4175 credits a recursion to Deliveries § D
  lemmas the live code never calls; Subscribe-Face's header lists
  `chainStep-caps` as a caller into the clique when nothing calls it.
- **`dry-tick-core`'s header** still claims independence from the caps/INV?
  bridging problem — WRONG (the anchor problem is exactly where it sits); fix
  when next editing Caps-Bridge.

## RECOVERY SHA: the retired multiset measure — `11a34db`

`git show 11a34db` restores the Dershowitz–Manna apparatus (524 lines: `_≺ᵛ_`,
`≺ᵛ-wf`, `rank`, `shells`, descent lemmas), deleted under the freeze's
source-retires-it exemption. **The scenario that brings it back:** the ANCHOR
PROBLEM resolution wants a well-founded multiset order — the classical
instrument for exactly that descent class. Restore from the SHA rather than
re-deriving `≺ᵛ-wf`.

## WRITING AN ASSEMBLY — the postulate-to-assembly conversion (the method)

For a parent postulate `P` with proven pieces `o₁…oₖ`, `P`'s type `T` is
unchanged; it becomes

```agda
postulate P-core : <type of o₁> → … → <type of oₖ> → T
P : T
P = P-core (λ {a} {b} → o₁ {a} {b}) … oₖ
```

`P-core` is equivalent to `P` exactly when every hypothesis is a PROOF. A
*function*-valued piece must be wired by its DEFINING EQUATION instead (`ΩAt`
in `.Measures` is the worked example) — passing the function type quantifies
over every inhabitant and makes the core strictly STRONGER.

Four rules, each of which otherwise costs a full build to rediscover:

1. **EXTRACT hypothesis types from source; never retype them.**
   `scripts/check-wiring.py`'s `signature_text` does it exactly.
2. **Pass every lemma ETA-EXPANDED with explicit implicits** —
   `(λ {n} {Γ} → f {n} {Γ})`. When a statement reduces away its own implicit
   (`share-live-novals` computes on a literal list), bare arguments give
   `Unsolved metas`; the eta form always works.
3. **Copied signatures drag in VOCABULARY the parent module does not import.**
   Collect the names in one pass; Agda stops at the FIRST scope error.
4. **ORDERING: a postulate cannot reference a definition below it.** `-core`
   sits where the postulate was; the definition sits after the last piece it
   consumes. `make wiring` section B3 reports violations — do not learn this
   from a failed typecheck.

## Build-cost rules (unchanged)

- Iterate in `agda/probe/` with minimal imports (~6 s loops against cached
  interfaces); land probe-green bodies in batches.
- At most TWO heavyweight checks at once (Subscribe-Face/Wet class, multi-GB).
- Never let two workers edit the same module.
- Detach long builds with `EXIT=$?` logs; pin the working directory in every
  build command; verify the run actually ran (`Checking` lines, not just exit
  codes).

## Active tasks → phases

Live list is the session task tool. Under THE TIER ORDERING LAW the standing
tasks split cleanly into ACTIVE (tier 1 + the two design questions) and PARKED
(everything tier 2 / tier 3), and the split is the schedule:

**ACTIVE — tier 1 and design:**
- **#30** THE ANCHOR PROBLEM — Phase 1b. The critical path; nothing in tier 1's
  top block moves until it is answered.
- **#17** `opIterD≤sizeCount-root` + `sub-charge-capsOK-lift` — Phase 2's
  symbolic attack and generalization repair, then Phase 3.
- **#4** P3 + P4 — Phase 2 for P4's statement doubt, Phase 3.3 for P3's grind.
- **#33 (PARTIAL)** merge-cert — the STATEMENT half only, as Phase 1a's design
  carve-out. Its six consumer rewrites are PARKED.

**PARKED behind tier 1 — recorded so it is not lost, not so it is picked up:**
- **#31** tier-2 statement repairs (`dispatchShare-wf`), and #33's six rewrites.
- Everything in roadmap Phase 4 and Phase 5.

**#19** and **#26** are COMPLETE (Phase 0). Note #19's answer — the two
structural arguments — doubles as `init-capsOK?-base-core`'s proof sketch.
