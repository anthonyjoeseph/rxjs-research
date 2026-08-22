# The seven emit leaves — order of work

## Landed
`emit-cap` is a REAL BODY over seven leaves.  Four clauses proven outright
(`emptyᵉ`, `μᵉ` at g0, `deferᵉ`, `varᵉ ()` absurd) — a burst with no `value`
event satisfies `burstND?` by computation at any bound.  All four `*All`
clauses share ONE leaf, because `innerNest sl (mergeAllᵉ b)` reduces to
`suc (innerNest sl b)` definitionally (`suc a + c ↝ suc (a + c)`).
Predicates are now type-indexed (`valND? sl C w v`), following `valCaps?`.

## 1. `emit-map` / `emit-scan` — the missing family member, and it is ADDITIVE
`nestDᵉ sl (mapᵉ f e) = nestDᵗ sl f + nestDᵉ sl e`.  So what the clause needs is

    nestD-applyFn : (f : Fn Γ [] [] [] (obs a) (obs b)) (v : Closed Γ a) →
      nestDᵉ sl (applyFn f v) ≤ nestDᵗ sl f + nestDᵉ sl v

ADDITIVE, and that is the whole point: `applyFn-size` (PROVEN, Measures.agda,
via `evalWith-size`) pays `(2 + 2·V) ^ (3 ^ sizeᵗ fn)` because substitution
duplicates subterms and SIZE counts every copy.  `nestDᵗ` joins them with `⊔`
(`pairᵗ`, `nestDᵗˢ`, `ifᵗ`) — the ⊔ repair — so duplication is free in this
currency and the bound stays additive.

ALREADY PROBED, without having been stated: `Probed.Nest-Depth` §3's
`emittedCap : nestDᵉ slots₀ emitted ≡ nestDᵉ slots₀ emitter` is this inequality
at `f = dupF`, the duplicating step function.  2 ≡ 2 under `⊔`; 3 ≡ 2 under a sum.

`emit-scan` wants the same lemma plus the `outWᵉ n sl e *` factor its clause carries.

## 2. `emit-input` — the scripted arms
Three of the four arms are provable and the type system supplies the reason:
`scripted` carries `{ok : T (isData t)}`, `isData` is HEREDITARY
(`isData (s ×ᵗ t) = if isData s then isData t else false`, `isData (obs _) = false`),
so no observable can hide in a scripted payload.  The lemma:

    valND?-isData : (w : Ty) → T (isData w) → (v : Val Γ w) →
      valND? sl C w v ≡ true

induction on `w`, splitting on `isData s` at the product and sum arms.  Then the
`hot` arm splits on `memberSource` (both sides value-free), `cold sync []`
and `cold sync (d ∷ ds)` emit `map value sync` and fall to the lemma.
The `shared` arm is the CONNECT and stays the leaf with content.
TRAP: `subscribeE` does `with Sched.slots sched i`, so the goal only reduces
if the clause splits on the same term — copy the technique from
`subscribeE-input-caps` (Subscribe-Face.agda), which already faces this.

## 3. `emit-of`, `emit-take`, `emit-mu`
`emit-of`: values are `map evalTm ts`, bound is `nestDᵗˢ sl ts` (a `⊔`) —
wants `nestDᵉ sl (evalTm t) ≤ nestDᵗ sl t`, the `applyFn` lemma's nullary case.
`emit-take`: `take-f` filters, so the emitted list is a sub-list of what the
recursion already bounded; `evalTm c` needs the same `with` technique as above.
`emit-mu`: `nestDᵉ sl (unfoldμ body) ≤ nestDᵉ sl body` — a substitution fact,
and `nestDᵉ sl (μᵉ e) = nestDᵉ sl e` means there is no slack to spend.
