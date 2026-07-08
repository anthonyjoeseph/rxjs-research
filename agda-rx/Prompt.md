In this folder, I'd like you to port a very simple implementation of `Observable` into agda. We're actually implementing `Instantaneous`, since we'll want batchSimultaneous, but let's just call it `Observable`

Observable should be implemented as simply as possible, using forkIO and MVars. (We should be using haskell's IO, btw, for maximum interop). Limit yourself to implementing the basic primitives including 'cold' and 'share' (to allow for constructing both cold & hot observables), and of course batchSimultaneous.

We also need a 'subscribe' function, which will exclusively serve as the entry-point: `function subscribe <A>(main: Observable<Unit>): IO<Unit> {}`. It should use `Unit` so as to discourage people from calling it more than once in their program

We don't care about Subjects at all - just `cold` and `share` will be plenty. `cold` should look like `function cold<A>(push: (emit: IO<A[]>) => IO<Unit>): Observable<A> {...}` (pardon my typescript syntax, I'm still an agda newbie), so that you're able to use IO to trigger an burst of 'synchronous' emissions

If you look inside `agda-rx/src`, you'll notice a module called `UniqueThing.agda` - that's the result of my spike. I think I found a way to represent the 'provenance' as a distinctly unique value, definitionally - so that each new call to `cold` will create a new `provenance`. The cool thing is - equality of these unique values is available to us at compile time. The idea is - this allows us to prove some things about Observables! Fairly weak things, probably, but that's the main desired feature here

I don't know if it'll work out, but I would also like for the proof & lemmas of `batchSimultaneous` to be useful to users of Observable. Or, if not those proofs exactly, then something closely related

Anyway, for this first phase of work, I just want to come up with the data type for Observable, and all of the its primitives as postulates. And I'd like to come up with a postulate for a formally verifying the batchSimultaneous implementation. I think we should be able to re-use

I want to emphasize - no working code! Just data types and postulates, while we're still sorting out the desired syntax here.
