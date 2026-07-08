# Problems With the Current Codebase

Don't just solve these! See the [Why We Need to Fundamentally Pivot](#why-we-need-to-fundamentally-pivot) section

Listed here because - these are fundamental problems that will probably arise in the post-pivot versions as well

Solving these first _may_ enable a quicker and easier implementation of the _real_ solutions, or it might be best to just start the real solutions from scratch. Who knows? Depends how I'm feeling when the time comes

## Exp Tree - Easy

- `Emissions` is a list of 'events' modeled by 'frame'
  - not terrible, but a little harder to wrap my head around
- 'cold' observables need to be modeled as well - they re-start on 'subscribe'

### Solution

- The `Emissions` type should change into a vector of type `ObservableInput`
- An `ObservableInput` is either labeled “hot”, in which case it’s simply a list of (async) values, or “cold”, in which case it gets the list of sync values and the list of async values
- “Hot” mirrors InstantSubject, while “cold” mirrors the new “cold” constructor in typescript
- Whenever a “cold” observable is “subscribed to”, it plays from the start, whereas a “hot” observable exists unchanging in global scope

## Exp Tree - Hard

- the Exp tree is unable to model rxjs 'expand' - an Observable who subscribes to itself

### Solution

- [Coinduction?](https://agda.readthedocs.io/en/latest/language/coinduction.html)
- working around the termination checker will be tricky...

## Agda Pure-Implementation

- the 'mealy machine' (which it turns out is just a State monad) input type is way too permissive
- it give each rx-naive operator access to 'every' emission that's taking place in that frame
- their definitions don't look much like the 'real' rx

### Solution

We definitely need some plumbing so the 'operator' input just `previous-state`x`actual value`, unadorned with extra information

But the main problem is - what gets stored in state? How do we represent the idea of a `merge`, for example - multiple subscriptions being stored & listened to at once?

I think it's a bad idea to directly model the idea of an operator directly dealing with its input observables, calling 'subscribe' and 'unsubscribe', storing subscriptions in state. How the hell to we model 'subscribe' callbacks without opening ourselves up to recursion? This is a termination-checking nightmare

We've bought a lot of power by implementing the primitives the way we did in typescript - we should be able to meaningfully abstract _over_ the idea of a subscription.

But! Whatever distance there is between our 'pure-implementation' and the 'rxjs real world', also needs to be explicitly modelled / accounted for. Maybe that looks like another fast-check linkage to typescript, or maybe that somehow looks like an agda proof - idk.

# What Worked

I'm very happy with a lot of the progress I made!

## Overall Shape of the Proofs

- `verify-batch-simultaneous` is THE proof
- equates `spec-batch-simultaneous` and `impl-batch-simultaneous`
- uses an Exp tree to represent the idea of "any possible combination of primitives"

- `spec-batch-simultaneous`
  - implements batch-simultaneous 'after the fact'
  - can see all emissions history at once, and simply batches them based on what makes sense in retrospect
  - more 'obviously true'

- `impl-batch-simultaneous`
  - only able to work step-by-step
  - exists in the 'present', cannot see into the 'future'
  - is a 'mealy machine' (Fable's term, actually just a state monad)

- README semantics - smaller proofs
  - the README defines our semantics via 'edge cases'
  - it's easy to read that way
  - I had the idea - let's formalize those 'edge cases'!
  - I wanted them to be more general than unit tests - they each say something interesting about the semantics
    - they turned out to all be different versions of the same lemma (with one exception, i think)
  - The readme links to the actual proofs too!
  - this ensures at compile time that any change to the semantics will always exist within the boundaries of what we already _know_ we want
    - or will provide us positive proof of a contradiction, if one arises

## Writing Process (minus the wrong turns I took)

- state `verify-batch-simultaneous` as a postulate _before anything else_
  - just stating it was really hard!
  - it also involves postulating `spec-batch-simultaneous` and `impl-batch-simultaneous`, which is super useful
    - that's how I came up with the "clairvoyant spec" and "state monad impl" stuff
  - aaaaaaand it has all turned out to be subtely wrong (see 'Problems' above)
    - but it's so good to know specifically what I need to change!
- build a quickcheck between `spec-batch-simultaneous` and `impl-batch-simultaneous`
  - the point of this is to nail down the actual `impl-batch-simulaneous`
  - if `impl-batch-simultaneous` is written incorrectly, then it will be impossible to prove `verify-batch-simultaneous`!
  - so, we at least want to be pretty sure that it's correct before we tackle the actual proof
  - if it's pretty close, then it will be clearer how any problems with the proof will be useful to fix the implementation
  - added a script that appends failing quickcheck cases to a `UnitTest.agda` module as type-level unit tests
    - this gave us a quickly growing automatically generated list of regression tests
    - faster & simpler than jest - just run the compiler, which we do after each change to the agda code anyway
- build a 'fast-check' link between typescript and `impl-batch-simultaneous`
  - practically, this helps us keep the agda implementation honest - we don't want to be able to do anything in agda that we can't do in typescript
  - theoretically, this is our '99% sure' link between the typescript & the agda implementations
  - the other 1% is hopefully covered by the visual similarity between the two algorithms
  - much simpler than building some kind of shared data-transformation DSL shared by both languages

# Learnings re: Using AI for Proofs (the wrong turns I took)

### the ai is not that smart - even Fable

- I gave it my typescript implementation and basically told it 'formalize & prove this - have at it'
- it went off and wrote a bunch of stuff - it got me so excited at first, but I wasn't really able to tell what it was doing
- I had assumed it had come up with an "overall theorem", like `verify-batch-simultaneous`
- actually, it was just building up a corpus of random 'proofs' that were meandering about, leading nowhere
- it was trying to 'build up' rather than 'dig down', but it wasn't even sure what it was trying to 'build up' to
- this shocked me when I realized it - it seems like such a basic, obvious oversight

### Fable doesn't know what's important

- at first, it was keeping _every_ piece of code, long after it had become unused
  - it was documenting some of it as 'backwards compatible' or 'legacy' or 'v1'
- I directed it to start pruning things that weren't used
- so - it deleted `cold()` and it took me a long time to realize it was gone
  - this pointed to another giant mistake it had made:
  - when implementing Exp trees, it assumed that every Observable was hot(!)
  - there was no notion of `cold()` built into it at all
  - Fable decided to leave `cold` out of the spec early on, and then that oversight caused it to be completely deleted

### Fable wants to do its own thing

- I specifically directed it to take a crack at solving `verify-batch-simultaneous`, 'removing as many postulates as it can'
- I was being careful, b/c I didn't have many tokens left to spend
- Fable went off and resolved all of the _other_ postulates, in the 'spec' and 'implementation' directories - aargh!

### Fable/Opus doesn't think to spend time coming up with tooling / efficiency improvements

- not unless you ask it to
- it's very happy to waste a lot of tokens
- even if a better process is obviously available
- it doesn't think outside of the immediate task you've given it

### I Have to Understand The Postulates

- it's ok if I don't understand how a proof is implemented
- but I truly cannot asume that Fable knows what I'm going for
- Fable kept finding 'choices' I needed to make to further refine the spec, as it was 'writing' my proof
  - this happened b/c of a miscommunication early on
  - and when I changed my mind, Fable really didn't want to heart it
  - and I was tentative b/c I had no idea was going on and I didn't want to break anything
  - ultimately, it turned out that the spec was very simple and consistent
  - but I didn't know that until much later, b/c I assumed the AI had completely defined it when it hadn't
- I assumed Fable knew what it was doing when it wrote the 'rx-naive' impl-side stuff
  - it turns out - it wasn't really faithfully modelling the behavior of rxjs
  - it was also giving each operator wayyy too much information
  - all of this unintentionally weakened the proof significantly
- I still don't really know how the spec is using monotonicList, come to think of it...

### Opus is plenty capable

- defining an approach
  - Fable came up with the Exp trees and I was floored - I had been trying to come up with that solution for months
  - I thought fable was uniquely good at that sort of thing
  - but, in retrospect, a much smaller model probably could have helped me come up with that. It's the standard approach to proving things about arbitrarily deeply nested syntax
  - I had been worried that Opus wouldn't be smart enough to come up with an 'overall approach'
  - turns out - Fable's not smart enough for that either!
  - but - what it turns out I actually want, is a _research assistant_ who can tell me common ways to approach a given problem
- writing proofs
  - Fable is probably smarter at this, as a baseline - it's able to 'think more steps ahead in the chess game'
  - but 'smarter' is not 'better' - Fable wastes a lot of resources doing its 'deep thinking', and these proofs are ultimately fairly straightforward. Stating them properly is the tricky thing
  - once all of the appropriate tooling was in place, Opus was able to take the ball and run really far with it - to the point that it helped me realize the fundamental problems with the approach (see [why we need to fundamentally pivot](#why-we-need-to-fundamentally-pivot))
  - if I were to keep working away at `impl-batch-simultaneous`, I would have told Opus to keep a list of 'failed attempts' in markdown - every time it took a 'path' to try to resolve some bug, and decided that 'path' was causing more problems than it was solving, it should _record_ that so that it learns from its mistakes
    - this sort of thing is much more efficient and useful than just chucking everything into Fable's gigantic & expensive context memory

### Opus is still kinda dumb though

- when quickcheck was timing out on certain tests, it determined that it was probably due to excessive Exp tree depth
- it put a timeout on the test cases - if execution exceeds the timeout, the test is considered 'passing' (!)
- this was clearly a disastrous train of thought
- I asked it - 'at what depth are the tests failing?' it said - four
- I said - 'that's not very deep, you should investigate further'
- it found out that - quickcheck was passing in very large natural numbers to represent observable emissions, which cause agda to use a huge amount of memory
- so the solution turned out to be fairly straightforward
- and I decided to put in a timeout - but it causes the test to 'fail' rather than 'pass'
- in conclusion: you need to pay attention to what it's doing

# Why We Need to Fundamentally Pivot

- the rxjs team probably isn't interested in anything short of `.subscribe` and `.unsubscribe` support

### RXJS solution

- while this is technically possible (I think) (I hope!) using a root-level provenance

- it's honestly a pain in the ass for the `.subscribe` user to receive and reason about an `InstEmit`
- it's equally good to give each '.next()' emission from the 'subscribers' its own provenance, rather than a separate provenance at the root
  - `cold(s => { s.next(1); s.next(2); })` and `hot.next(1); hot.next(2)`
  - just wrap these `.next()` calls with a provenance thingy
  - and define mergeAll() , concatAll() etc to use this logic:

> the id is per cascade, so multiple emissions share it — and a synchronously-spawned inner must inherit the trigger's id, not mint a fresh one. In merge(mergeMap(v => of([v*10]))(s), s), the of([50]) fires inside s's instant, so its 50 carries T; only the inner's later, async emissions mint new ids. So it's not "every emission stamps itself" — it's "every emission carries the id of the .next() at the root of its synchronous cascade," threaded down through spawns.

So the model becomes:

- source .next() mints a fresh instant id (the one remaining bit of state, at the leaves),
- map / merge / scan copy it (pure),
- joins stamp their inner's synchronous flush with the trigger's id, its async tail with fresh ids (that sync/async split is what batchSync is for, per-inner),
- batchSimultaneous groups consecutive same-id — a pure scan, no registrations, no counting.

### Agda solution

- here, keeping Provenance at the root makes sense b/c we're able to model it very nicely as a unique value at compile time (!)
  - see 'agda-rx/UniqueThing.agda`
- this will give us the ability to create a `_shares-sources_` type predicate
  - will be inhabited if two Observables share at least one source
  - this means that it's _possible_ that they might emit at the same time (though they may not)

- this probably _does not_ give us the ability to 'prove' things about the observables themselves
- this _does_ point towards the ability to restrict certain undesirable syntax
  - we use `uniqueness` alongside other type-level information
  - inspired by rxjs traits - https://github.com/cartant/rxjs-traits

- in a world where `map` and `scan` only accept `canonical` functions, (e.g. canonical normal form, for boolean expressions)
  - we model the entire syntax tree as a type
  - we gain equality & proofs at compile-time
  - we gain the ability to 'reduce' observable trees into _their_ canonical forms
  - this includes 'simultenous' observables literally pointing to the same thread in memory

- we should share as much code as possible between the 'pure-implementation' and the 'io-implementation' sides
  - we'll never truly be able to 'prove' anything about IO
  - but the closer we keep these, the more convincing the proofs
