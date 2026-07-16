export type Provenance = number | symbol;
export type InstEmit<A> = {
  prov: Provenance;
  val: A;
};
