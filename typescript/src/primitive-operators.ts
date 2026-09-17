import {
  Observable,
  defer as rxDefer,
  filter,
  map as rxMap,
  merge,
  share as rxShare,
  mergeMap,
  of as rxOf,
  scan as rxScan,
  takeWhile,
  tap,
} from "rxjs";
import {
  CutLedger,
  InstEmit,
  InstEvent,
  SUBSCRIBE_FRAME,
  SourceId,
  cutLedgerStep,
  cutVictimCloses,
  emptyCutLedger,
  mergeAllBurst,
  openAfter,
  reassemble,
  splitEmit,
} from "./inst-emit.js";
import { Driver, oneShotArrival } from "./driver.js";
import {
  Bracketed,
  Marked,
  SYNC_END,
  UPSTREAM_DONE,
  bracketSync,
  markSync,
} from "./constructors.js";

export { exhaustAll, mergeAllAll, switchAll } from "./join.js";

// a one-shot subscription burst (Agda's oneShotBurst): a source that
// lives and dies inside its own subscribe frame — init, its values,
// close, complete — one emit, minting a fresh source per subscription
// and inheriting the instant live at subscribe time (id-inheritance).
export const of = <A>(driver: Driver, input: A[]): Observable<InstEmit<A>> =>
  rxDefer(() => {
    const source = driver.mintSourceId();
    return rxOf<InstEmit<A>>({
      events: [
        { type: "init", source },
        ...input.map((value) => ({ type: "value", value }) as const),
        { type: "close", source, reason: "exhausted" },
        { type: "complete" },
      ],
      instant: SUBSCRIBE_FRAME,
      source,
      kind: "subscribe",
    });
  });

// oneShotBurst [] — init, close, complete, no values
export const empty = (driver: Driver): Observable<InstEmit<never>> =>
  of<never>(driver, []);

// The slot-telescope share IS rxjs's own `share` with every reset
// turned off (Anthony) — connect once at the first subscription, never
// disconnect (an unobserved share keeps burning arrivals), latch
// completion forever. That ruling is what let the hand-rolled connect
// go: rxjs holds the one upstream subscription and the fan-out, and
// what is left here is the protocol traffic around it. Mirrors Agda's
// subscribeSharedSlot + dispatchShare:
// - the connect burst flows up the FIRST subscriber only, retagged
//   plumbing (its registrations belong to the share, not to any
//   operator it flows through);
// - each upstream arrival emits the emptied pass-through with a
//   `handoff` announcement straight to the root (driver.pushChainEmit),
//   then one fan-out emit per subscriber, all in the same instant;
// - the completion latch flips BEFORE the final fan-out (a Subject
//   closes before delivering its completion): a subscriber joining
//   mid-final-cascade — or any time later — gets the immediate
//   init/close/complete one-shot, never a registration dropped
//   without its close. Completion is re-observable, values are not.
// DEAD ROUTE -- the two latches below do NOT come out the way the
// registration count did.  That one was a cell between two folds and
// moved onto the signal joining them, so the dependency became the
// type's.  These are different: both are read at SUBSCRIBE time, to
// decide what kind of subscriber this is, and the thing they are really
// asking is "did someone get here first".
//
// Three routes tried, each dead for its own reason.  Deriving the answer
// from a REPLAYED signal stream (rxjs `share` with a `ReplaySubject`
// connector) hands a late subscriber the whole history, burst signals
// included -- but a replay arrives in the subscriber's own subscribe
// frame and so does a genuine connect burst, so the scan cannot tell
// them apart, and `markSync` does not separate them either.  Reading a
// derived status stream before building the pipeline is worse than
// indistinguishable: subscribing it CONNECTS the upstream, the burst
// fires into it, and the first subscriber's own scan then misses the
// burst entirely.  And rxjs tracks a refCount internally without
// exposing it, so there is no operator that answers the question.
//
// So "first subscriber" is a fact about subscription ORDER and not
// about anything in the stream, which is why no rearrangement of the
// folds reaches it.  The repair is not a cleverer pipeline -- it is a
// share in which no subscriber is special, and that is a design change
// to the protocol rather than to this function.
export const share = <A>(
  driver: Driver,
  obs: Observable<InstEmit<A>>,
  source: SourceId,
): Observable<InstEmit<A>> => {
  let connected = false;
  let completed = false;

  const latchedOneShot = (): InstEmit<A> => ({
    events: [
      { type: "init", source },
      { type: "close", source, reason: "exhausted" },
      { type: "complete" },
    ],
    instant: SUBSCRIBE_FRAME,
    source,
    kind: "subscribe",
  });

  const initEmit = (extra: InstEvent<never>[]): InstEmit<A> => ({
    events: [{ type: "init", source }, ...extra],
    instant: SUBSCRIBE_FRAME,
    source,
    kind: "subscribe",
  });

  // THE CONNECT BURST AND THE LATER ARRIVALS ARE DIFFERENT TRAFFIC, and
  // telling them apart used to be what forced the manual subscription:
  // a burst emit is the def coming alive and rides up the first
  // subscriber retagged `plumbing`, while an arrival mints a chain emit
  // and fans out. `bracketSync` draws that line as a VALUE, so the
  // upstream can be an ordinary pipeline — and because it sits BELOW
  // the share, the fold runs once, which is what makes its writes to
  // its registration tracking and its completion latch the share's own
  // bookkeeping rather than a per-subscriber copy. `endWith` is what
  // recovers an upstream that rx-completed inside the burst without
  // closing its registrations: the marker arrives before SYNC_END
  // exactly when the completion was synchronous.

  // THE OPEN REGISTRATIONS RIDE THE `connected` SIGNAL rather than a
  // cell, because the two scans that need them are different folds: the
  // count is WRITTEN by this one and READ by the first subscriber's,
  // and a cell between them is correct only while this fold happens to
  // run first. It does — it is upstream — but that is subscription
  // order standing in for a data dependency, so the count goes in the
  // signal that marks the boundary and the dependency is the type's.
  type Signal =
    | { tag: "burst"; emit: InstEmit<A> }
    | { tag: "connected"; spent: boolean; openCount: number }
    | { tag: "fanout"; emit: InstEmit<A> };

  const signals: Observable<Signal> = markSync(obs).pipe(
    rxScan<
      Marked<InstEmit<A>>,
      {
        live: boolean;
        spent: boolean;
        fin: boolean;
        open: SourceId[];
        out?: Signal;
        // the chain's own emit, emptied of values, announcing the
        // handoff — it reaches the root directly (Agda foldPath's
        // share-sink clause) rather than through any subscriber's
        // pipeline, so it leaves this fold as a RESULT and is sent
        // below. Sending it from inside the accumulator would make
        // this scan's answer depend on when it ran and not only on
        // what it was handed.
        chain?: InstEmit<never>;
      }
    >(
      (state, item) => {
        if (item === UPSTREAM_DONE)
          return {
            ...state,
            spent: true,
            fin: false,
            out: undefined,
            chain: undefined,
          };
        if (item === SYNC_END)
          return {
            ...state,
            live: true,
            fin: false,
            chain: undefined,
            out: {
              tag: "connected",
              spent: state.spent,
              openCount: state.open.length,
            },
          };
        const open = openAfter(item, state.open, true);
        if (!state.live)
          return {
            ...state,
            open,
            fin: false,
            chain: undefined,
            out: { tag: "burst", emit: item },
          };
        const parts = splitEmit(item);
        const fin = parts.fin || open.length === 0;
        if (fin) completed = true; // latch BEFORE the final fan-out
        return {
          live: true,
          spent: state.spent,
          open,
          fin,
          chain: {
            events: [...parts.bookkeeping, { type: "handoff", source }],
            instant: item.instant,
            source: item.source,
            kind: item.kind,
          },
          out: {
            tag: "fanout",
            emit: {
              events: [
                ...(fin
                  ? [{ type: "close", source, reason: "exhausted" } as const]
                  : []),
                ...parts.values.map(
                  (value) => ({ type: "value", value }) as const,
                ),
              ],
              instant: item.instant,
              source,
              kind: "delivery",
            },
          },
        };
      },
      { live: false, spent: false, fin: false, open: [] },
    ),
    // the chain emit leaves here rather than from inside the fold, and
    // it leaves ABOVE the share below, so it is sent once for the def
    // and not once per subscriber
    tap((state) => {
      if (state.chain !== undefined) driver.pushChainEmit(state.chain);
    }),
    takeWhile((state) => !state.fin, true), // the final fan-out, then done
    filter((state) => state.out !== undefined),
    rxMap((state) => state.out as Signal),
    rxShare({
      resetOnRefCountZero: false,
      resetOnComplete: false,
      resetOnError: false,
    }),
  );

  const fanouts = signals.pipe(
    filter((s): s is Signal & { tag: "fanout" } => s.tag === "fanout"),
    rxMap((s) => s.emit),
  );

  return rxDefer(() => {
    if (completed) return rxOf(latchedOneShot());
    if (connected) return merge(rxOf(initEmit([])), fanouts); // join mid-flight
    connected = true;
    // the first subscriber is the one the connect burst flows up, and
    // its init is emitted AT the boundary rather than before it: the
    // burst decides whether that init already carries its close, and
    // nothing observable is reordered because the whole group is one
    // frame.
    return signals.pipe(
      rxScan<
        Signal,
        { burst: InstEmit<A>[]; done: boolean; out: InstEmit<A>[] }
      >(
        (state, s) => {
          if (s.tag === "burst")
            return { burst: [...state.burst, s.emit], done: false, out: [] };
          if (s.tag === "fanout")
            return { burst: [], done: false, out: [s.emit] };
          const flat = mergeAllBurst(state.burst);
          const burstFin =
            s.spent ||
            flat.done ||
            (state.burst.length > 0 && s.openCount === 0);
          // the def died inside its own connect burst: latch; this
          // registration closes in the same instant
          if (burstFin) completed = true;
          return {
            burst: [],
            done: burstFin,
            out: [
              initEmit(
                burstFin
                  ? [{ type: "close", source, reason: "exhausted" }]
                  : [],
              ),
              ...state.burst.map((emit): InstEmit<A> => ({
                ...emit,
                kind: "plumbing",
              })),
            ],
          };
        },
        { burst: [], done: false, out: [] },
      ),
      takeWhile((state) => !state.done, true),
      mergeMap((state) => rxOf(...state.out)),
    );
  });
};

// mintᵉ: one fresh source token per SUBSCRIPTION, handed to the body and
// nothing else. No event, no registration, no hop — the operator wrapping
// the binder owes those. `rxDefer` is what makes it per-subscription
// rather than per-pipeline, which is the whole of the semantics.
export const mint = <A>(
  driver: Driver,
  compileBody: (token: number) => Observable<InstEmit<A>>,
): Observable<InstEmit<A>> => rxDefer(() => compileBody(driver.mintSourceId()));

// deferᵉ (NOT rxjs defer): lazy PLUS a one-tick hop, the body's
// emissions minting fresh ids (an async boundary). Mirrors Agda's
// deferᵉ clause: init in the subscriber's instant; when the hop fires
// the body is subscribed and its sync burst is grafted behind the
// hop's close into ONE delivery emit (Agda's thru-outer mergeAllᵒ walk) —
// the body thunk runs AT FIRE TIME, which is what breaks μ's
// unfolding regress: each unfolding costs a schedule hop.
export const defer = <A>(
  driver: Driver,
  compileBody: () => Observable<InstEmit<A>>,
): Observable<InstEmit<A>> =>
  rxDefer(() => {
    const source = driver.mintSourceId();
    return merge(
      rxOf<InstEmit<A>>({
        events: [{ type: "init", source }],
        instant: SUBSCRIBE_FRAME,
        source,
        kind: "subscribe",
      }),
      oneShotArrival(driver, driver.currentTick() + 1).pipe(
        mergeMap(({ instant }) =>
          // the body's burst is regrouped by a FOLD over the bracketed
          // stream rather than accumulated by a subscriber: everything
          // before SYNC_END is the burst, the marker itself is where
          // the one delivery emit comes out, everything after is the
          // body's async tail passing through under its own envelope.
          // rx completion needs no special case — if the body finished
          // inside its burst the merged stream completes on its own;
          // `takeWhile` covers the other exit, a body that signalled
          // done through its events without completing.
          bracketSync(compileBody()).pipe(
            rxScan<
              Bracketed<InstEmit<A>>,
              { burst: InstEmit<A>[]; done: boolean; out?: InstEmit<A> }
            >(
              (state, item) => {
                if (item !== SYNC_END)
                  return state.out === undefined && !state.done
                    ? { burst: [...state.burst, item], done: false }
                    : { burst: [], done: state.done, out: item };
                const flat = mergeAllBurst(state.burst);
                return {
                  burst: [],
                  done: flat.done,
                  out: reassemble(
                    { instant, source, kind: "delivery" },
                    [{ type: "close", source, reason: "exhausted" }],
                    flat.bookkeeping,
                    flat.values,
                    false,
                  ),
                };
              },
              { burst: [], done: false },
            ),
            takeWhile((state) => !state.done, true),
            filter((state) => state.out !== undefined),
            rxMap((state) => state.out as InstEmit<A>),
          ),
        ),
      ),
    );
  });

// map and scan: THE pure-function formers, and there are two because
// rxjs has two. A step reads ONE value -- and, for scan, the state
// carried across it -- and returns one value. That is the whole
// interface, and what it EXCLUDES is the point: a step mints no
// registration, reads none of the bookkeeping, cannot end the stream
// and cannot see which instant it is in -- so the emit's own events and
// its fin bit ride through untouched and the protocol is not something
// a program can write.
//
// THE STEP IS POINTWISE AND THE EMIT IS NOT, which is the one thing to
// carry when reading either body. An emit carries a LIST of values, so
// each operator runs its step once per element and rebuilds the emit
// around the results; a frame is never something the step can see, and
// that is what stops a program writing one.
//
// NEITHER IS DERIVABLE FROM THE OTHER. A scan's accumulator IS its
// output, so changing the value's type needs a seed at the new type,
// and the value language has no generic inhabitant to default one to; a
// map carries no state, so it cannot stand in for a scan either.
export const map = <A, B>(
  obs: Observable<InstEmit<A>>,
  fn: (a: A) => B,
): Observable<InstEmit<B>> =>
  obs.pipe(
    rxMap((emit) => {
      const { bookkeeping, values, fin } = splitEmit(emit);
      return reassemble(emit, bookkeeping, [], values.map(fn), fin);
    }),
  );

export const scan = <A, S>(
  obs: Observable<InstEmit<A>>,
  initial: S,
  step: (state: S, value: A) => S,
): Observable<InstEmit<S>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { state: S; out?: InstEmit<S> }>(
      (carried, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const out = values.reduce<{ state: S; emitted: S[] }>(
          (acc, value) => {
            const next = step(acc.state, value);
            return { state: next, emitted: [...acc.emitted, next] };
          },
          { state: carried.state, emitted: [] },
        );
        return {
          state: out.state,
          out: reassemble(emit, bookkeeping, [], out.emitted, fin),
        };
      },
      { state: initial },
    ),
    rxMap((carried) => carried.out as InstEmit<S>), // the seed is never emitted, so out is set
  );

// batchSync-f: the one plain operator that can see synchrony, and it
// sees exactly one bit of it — whether the emit it is regrouping was
// pushed during its own subscribe call. An emit inside that burst
// leaves as ONE group, head and tail (Agda's groupSync, so an empty
// emit yields no group at all); every later emit's values leave as
// singletons (soloSync). There is no accumulator and there cannot be:
// holding a value back to see whether another joins it would need to
// know that another is owed, which is the forward-looking knowledge
// this operator is defined not to have.
//
// THE BIT COMES FROM rxjs's OWN SUBSCRIBE ORDERING, NOT FROM A
// SUBSCRIPTION THIS OPERATOR OWNS. `bracketSync` merges a marker after
// the source, and `merge` subscribes its inputs in order and
// synchronously, so the source drains its whole subscribe burst before
// the marker is subscribed and fires. The marker therefore lands
// exactly at the boundary, in the same frame, with no hop and no
// timing change — which is what lets the split arrive as a VALUE that
// a scan reads, rather than as a callback an operator drives.
export const batchSync = <A>(
  obs: Observable<InstEmit<A>>,
): Observable<InstEmit<[A, A[]]>> =>
  bracketSync(obs).pipe(
    rxScan<Bracketed<InstEmit<A>>, { sync: boolean; out?: InstEmit<[A, A[]]> }>(
      (carried, item) => {
        if (item === SYNC_END) return { sync: false };
        const { bookkeeping, values, fin } = splitEmit(item);
        const groups: [A, A[]][] = carried.sync
          ? values.length === 0
            ? []
            : [[values[0], values.slice(1)]]
          : values.map((v): [A, A[]] => [v, []]);
        return {
          sync: carried.sync,
          out: reassemble(item, bookkeeping, [], groups, fin),
        };
      },
      { sync: true },
    ),
    filter((carried) => carried.out !== undefined),
    rxMap((carried) => carried.out as InstEmit<[A, A[]]>),
  );

// take-f: forward the first `emissions` values, then cut. The cut emit
// carries the taken prefix plus a `close … cut` for EVERY registration
// still open through this operator (Agda's cutThrough) — tracked from
// the init/close bookkeeping that flowed through, this emit's own
// events applied first (a registration whose exhausted close rides the
// cutting emit is already closed, never closed twice) and plumbing
// excluded (a share's connect traffic is not ours to cut). Then the
// stream completes — rx teardown cancelling any scheduled deliveries
// (Agda's sweepLive). Count 0 is routed to `empty` by the compiler
// (Agda: take 0 never subscribes its source), so `emissions ≥ 1` here.
//
// AND IT IS NOT A PURE-FUNCTION FORMER, WHICH IS THE PALETTE'S DIVIDING
// LINE DRAWN AT THE ONE OPERATOR THAT LOOKS LIKE IT SHOULD BE ONE.
// `map` and `scan` pass the test because a step reading one value
// decides everything they emit.  This one reads the open-registration
// multiset and the cut ledger, MINTS bookkeeping (one close per victim,
// with a per-victim reason), and raises fin on the emit that cuts.  A
// step that could do that would be a step handed source ids, close
// reasons and emit kinds -- the protocol's own vocabulary, in the value
// language, writable by a program.  So `take` stays a former of its own.
export const take = <A>(
  obs: Observable<InstEmit<A>>,
  emissions: number,
): Observable<InstEmit<A>> =>
  obs.pipe(
    rxScan<
      InstEmit<A>,
      {
        remaining: number;
        cut: boolean;
        open: SourceId[];
        ledger: CutLedger;
        out?: InstEmit<A>;
      }
    >(
      (state, emit) => {
        const { bookkeeping, values, fin } = splitEmit(emit);
        const open = openAfter(emit, state.open, false);
        const ledger = cutLedgerStep(emit, state.ledger);
        const taken = values.slice(0, state.remaining);
        const didCut = taken.length === state.remaining; // filled the quota
        if (!didCut)
          return {
            remaining: state.remaining - taken.length,
            cut: false,
            open,
            ledger,
            out: reassemble(emit, bookkeeping, [], taken, fin),
          };
        // per-victim reasons from the ledger (paid or born this
        // instant ⇒ cut, else cutPending); the cut RAISES fin on this
        // very emit (Agda take-f returns fin′ = true) — a downstream
        // join absorbs it, the root keeps it
        return {
          remaining: 0,
          cut: true,
          open: [],
          ledger,
          out: reassemble(
            emit,
            bookkeeping,
            cutVictimCloses(open, ledger, emit.instant),
            taken,
            true,
          ),
        };
      },
      { remaining: emissions, cut: false, open: [], ledger: emptyCutLedger },
    ),
    takeWhile((state) => !state.cut, true), // include the cutting emit, then complete
    rxMap((state) => state.out as InstEmit<A>), // the seed is never emitted, so out is set
  );

// the ROOT materializes the fin bit as a `complete` EVENT on the
// DELIVERY emit that closes the last live registration (Agda
// foldPath's root clause — it only runs on arrival cascades; in the
// subscribe frame, complete events are minted in-band: one-shots at
// their mint site, take's cut and a spent join at the frame that
// raises fin, exactly Agda's pushBurst). Applied once, over the full
// root stream (pipeline output MERGED with the driver's chain emits:
// the ledger must see a share's plumbing inits AND the chain-emit
// closes that retire them). Appends at most once; a share's valueless
// chain traffic after root completion is left untouched, and a
// transient empty ledger inside the subscribe frame (a connect-died
// share's [init, close] before its plumbing burst) never triggers.
export const materializeCompletion = <A>(
  obs: Observable<InstEmit<A>>,
): Observable<InstEmit<A>> =>
  obs.pipe(
    rxScan<InstEmit<A>, { open: SourceId[]; done: boolean; out?: InstEmit<A> }>(
      (state, emit) => {
        const open = openAfter(emit, state.open, true);
        const alreadyFin = emit.events.some((ev) => ev.type === "complete");
        const materialize =
          !state.done &&
          !alreadyFin &&
          open.length === 0 &&
          emit.kind === "delivery";
        return {
          open,
          done: state.done || alreadyFin || materialize,
          out: materialize
            ? { ...emit, events: [...emit.events, { type: "complete" }] }
            : emit,
        };
      },
      { open: [], done: false },
    ),
    rxMap((state) => state.out as InstEmit<A>), // the seed is never emitted, so out is set
  );
