// fixture: the generator writes type tags of every kind, formers and not
const natT: Ty = { type: "nat" };
const genTm = () => ({ type: "natT", ty: natT, val: 3 });
const genExp = () => ({ type: "lift", ty: natT, src: leaf });
const genDefer = () => ({ type: "defer", ty: natT, body: b });
// an operator over a nat pair is picked out of a list; one over anything else
// is written on its own, and a bare scan for the quoted word would pass on
// a quoted "not" anywhere else in the file -- as here
const genPrim = () => pick(["add"] as PrimOp[]);
const genNot = () => ({ op: "not", arg: b });
