# Agda language and stdlib traps

Traps **inside the language**; build and tooling traps live in
[agda-build.md](agda-build.md). Each cost real time at least once, and most share a shape:
**Agda reports them against the WRONG thing.** Read the entry before reasoning from the error.

## Trap style guide

- bad agda code example, in markdown
- good agda code example
- sentence fragment explaining the advantage to the 'good' version

The bad/good examples should be as brief as possible, under 7 lines if possible.
Expressiveness is much better than formal correctness — make heavy use of pseudocode
conventions.

Read thru all examples before adding a new one — make sure you're not adding anything
redundant. Always better to augment an existing example, or, best of all, leave everything
as-is.

---

## Names

### A binder collides with something in scope

```agda
f (acc hs) = …        -- "hs is not a constructor of _≤_"  (hs is a constructor somewhere)
g (consᵗ a as) = …    -- NoParseForLHS, "Operators used: None"  (`as` is a mixfix name part)
```
```agda
f (acc hs′) = …       -- after `grep 'hs :'`
g (consᵗ a xs) = …
```
Your variable stays a variable. "X is not a constructor of T" → grep `X :`; an LHS that
won't parse with every constructor in scope → suspect the binders, rename one letter.

### A `variable` block generalises in declaration order

```agda
variable n : ℕ ; Γ : Ctx n
lemma : P Γ → Q n      -- "Γ.n != n", or an out-of-scope variable in a well-formed type
```
```agda
lemma : ∀ {n} {Γ : Ctx n} → P Γ → Q n
```
One name per number, binders in the order you wrote — use `variable` only for
single-binder signatures.

### Inside `abstract`, every `where` binding needs a signature

```agda
abstract
  S-lemma = … step … where step = …    -- MissingTypeSignatureForOpaque + a desugared dump
```
```agda
abstract
  S-lemma = … step … where step : T ; step = …
```
Agda never infers an abstract type; the dump is Agda's own rendering, not mangled source.

## Unsolved metas — an implicit nothing in the term determines

```agda
… ∧-true _ _ …             -- the goal reduced its own ∧ away
… +-monoˡ-≤ (s≤s z≤n) …     -- z≤n's implicit; and implicits under _+_ (≤-refl won't invert _+_)
f = all (λ v → P v) vs       -- P's implicit {e}: a fresh meta per element
… hopDᵉ (inputᶜ i) …        -- inputᶜ's Γ appears only in its RESULT type
… T (p k x) … root …        -- T forgets k; root : Path Γ lo t t leaves lo free
… scan-st (evalTm s) …      -- existential index: no error, Agda normalises the conclusion looking for it
```
```agda
… ∧-true b c …
… +-monoˡ-≤ (s≤s (z≤n {k})) …
f {e = e} = all (λ v → P {e = e} v) vs
… hopDᵉ (inputᶜ {Γ = Γ} i) …
… f {lo = 1} … root …       -- census every application with one grep; pin them together
… scan-st {A = A} (evalTm s) …
```
The meta closes over a variable instead of asking the unifier. When a meta is blamed on an
application whose arguments look determined, look for an argument whose type variable
appears in its result only. A meta with no error and only a growing heap is the
existential-index case: 18 s pinned against 14 GB unpinned.

## Cost — the checker runs what it unfolds

A slow check is charged to the definition that TRIGGERS the unfolding, not the large one.
Cap the heap (`agda +RTS -M4G -RTS`) so it fails fast, and profile
(`make bg T=check F=… AGDA_PROFILE="--profile=definitions"`) before rewriting anything.

### A `with` normalises its head and pays for its context

```agda
f c with agrees c                 -- runs evaluate↓ symbolically: OOM, no error
g x with lemma x                  -- only destructures a Σ / splits a ⊎: pays for the whole context
... | (r , d) = …
```
```agda
f c = helper (agrees c)           -- or a non-dependent eliminator: maybe′, [_,_]′
g x = let (r , d) = lemma x in …  -- refl / Dec / indexed constructor: match in a small helper
```
Nothing gets abstracted over the context, so nothing gets normalised.

### A transparent definition unfolds into its consumers

```agda
tbl = record { …many fields… }             -- unfolded at every conversion that meets it
row : enter (capprox N n o env) p q e      -- whnf'd for implicit insertion: runs the denotation
d = let … in …                             -- unfolds into every consumer's `with`
```
```agda
opaque
  tbl = record { … }                       -- own lemmas `unfolding tbl`
  Row o p q e = enter (capprox N n o env) p q e  -- step lemmas once, over a variable program
```
Opaque names compare by argument, so two spellings of one program meet cheaply; a
consumer that only passes the value on never notices.

### A big closed numeral meets a variable

```agda
U = 10^44 ; … 1 + U … (with j free)      -- falls off GMP, peels U one suc at a time
```
```agda
step : ∀ a b → … a … b …                 -- state over variables, apply at the obligation's spellings
… step U j …                              -- pass implicits explicitly; proj₁/proj₂, not `with`
```
Keeps the numeral away from the variable; shrinking it doesn't help, the peel is linear.

## Arithmetic

### `_+_`, `_*_` and `≤ᵇ` match on the LEFT

```agda
∀ j → P (k + j)         -- k-deep suc-tower; under _*_ a degree-d subject costs (k+1)^d
solve … (V + 3) …
rewrite *-identityʳ     -- suc sz * 1 = suc (sz * 1): the inner product is untouched
bad : T (not (suc m ≤ᵇ n))  -- won't reduce as written
```
```agda
∀ j → P (j + k)         -- stuck, neutral; spend k ≤ S with subst over m∸n+n≡m
solve … (3 + V) …
rewrite *-identityʳ | *-identityʳ
ok : T (not (m <ᵇ n))   -- what it unfolds to; drop a cons via ≤ᵇ⇒≤ / ≤-trans / ≤⇒≤ᵇ
```
Spell terms the way the left-matching clauses actually leave them.

## `with` and carried premises

```agda
f h with lookupNode nid (nodes st)    -- h : P (lookupNode …): rewritten to P <pattern>, reduced
... | c = callee h                    -- UnequalTerms at the argument
```
```agda
f h with lookupNode nid (nodes st) in eq
... | c = callee (subst (λ z → P z ≡ true) (sym eq) h)  -- bare eq the other way round
```
`in` names the scrutinee without a pattern position. Better still, let the proof and the
lookup share ONE `with`, so refining one refines the other and no equation is needed.

## Termination

### Bisect on a subset of the block

```agda
mutual a … ; b … ; c … ; d … ; e …     -- one error naming every member
```
```agda
mutual a … ; b …  ;  postulate c d e   -- then route one call edge at a time to a postulated copy
```
Only the loops among the survivors are left to check, and that is much faster.

### A `with`, an alias or an as-pattern rebuilds what was matched

```agda
f (acc rs) with b … | _ = f (acc rs)   -- with-function gets the FIELD rs: unrelated, not equal
g (suc (suc j)) = … g j′ where j′ = j  -- where-bound alias of the pattern
h aU@(acc fU) … = h aU …               -- as-pattern handed back is rebuilt
```
```agda
f (acc rs) = f′ (decide b) (acc rs)    -- decide outside the cycle: let for Σ, eliminator for Bool
g (suc (suc j)) = … g j …              -- inline it
h (acc fU) … = go … where go = …       -- one nested where-level per lexicographic component
```
The recursive call receives the argument that was matched, so it is visibly smaller. The
error names every call, and reads as a bad measure rather than a pattern problem.

### A lambda strips a copattern's guard; a `with` keeps it

```agda
fold … = [ (λ x → succ x) , … ]′ d     -- successor is an ARGUMENT of [_,_]′: unguarded
```
```agda
fold … with d
... | inj₁ x = succ x                   -- head of a with-branch, under a constructor: guarded
```
The successor sits under the copattern it answers. This pulls opposite to the previous
entry: drop `with` where an `acc` is matched, keep it where a guarded successor is built.

## Runtime — a pattern `let` runs its right-hand side per component

```agda
let (r , d) = eval … in b      -- b[proj₁ E, proj₁ (proj₂ E)]: E evaluated per use, compounding
let x = E in … x … x …          -- same
```
```agda
E |>′ λ (r , d) → b            -- runtime modules; definitionally equal; write implicit lambdas out
fold … with E … | (r , d) = b   -- in a fold copattern building the successor (keeps the guard)
fold (acc rs) … = helper E (acc rs)  -- …and if it also re-applies acc rs: helper in the mutual block
```
E is passed as one argument, so it is evaluated once. Nothing reports this but the clock.
