export type Exp =
  | { type: "lift"; ty: Ty; src: Exp }
  | { type: "sharedSig"; ty: Ty }
  | { type: "defer"; ty: Ty; body: Exp };

export type Tm = { type: "natT"; ty: Ty; val: number };

export const mapE = (): Exp => ({ type: "lift", ty: natT, src: e });
