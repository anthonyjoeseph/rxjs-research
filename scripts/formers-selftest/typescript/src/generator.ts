// fixture: the generator writes type tags of every kind, formers and not
const natT: Ty = { type: "nat" };
const genTm = () => ({ type: "natT", ty: natT, val: 3 });
const genExp = () => ({ type: "lift", ty: natT, src: leaf });
const genDefer = () => ({ type: "defer", ty: natT, body: b });
