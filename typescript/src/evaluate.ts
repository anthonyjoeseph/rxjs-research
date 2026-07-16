export type Tick = number;
export type Fuel = number;
export type Ordinal = number;

export type Timed<A> = {
  wait: number; // gap
  val: A;
};

export type ObservableInputCold<A> = {
  type: "cold";
  sync: A[];
  async: Timed<A>[];
};

export type ObservableInputHot<A> = {
  type: "hot";
  async: Timed<A>[];
};

export type ObservableInput<A> = ObservableInputCold<A> | ObservableInputHot<A>;

export type TestCase = {
  fn: (...params: any[]) => any;
  params: any[];
};

export declare const evaluate: (
  operator: TestCase,
  fuel: Fuel,
) => Promise<unknown[]>;
