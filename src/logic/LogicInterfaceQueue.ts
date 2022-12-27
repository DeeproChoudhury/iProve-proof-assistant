import { current, isDraft } from "immer";
import { useIProveStore } from "../store/store";
import * as AST from "../types/AST";
import { LI, LogicInterface, ProofOutcome } from "./LogicInterface";

export class LogicInterfaceQueue {
  li: LogicInterface;
  #current: Promise<unknown>;

  constructor(li: LogicInterface) {
    this.li = li;
    this.#current = Promise.resolve();
  }

  queue(fn: () => void) {
    this.#current = this.#current.then(fn)
  }

  queueEntails(reasons: AST.Line[], goal: AST.Line, cb: (outcome: ProofOutcome) => void) {
    this.li.setDeclarations(useIProveStore.getState().declarations.map(s => s.parsed).filter((s): s is AST.Line => !!s));
    this.li.setTypes(useIProveStore.getState().typeDeclarations.map(s => s.parsed).filter((s): s is AST.TypeDef => !!s && s.kind === "TypeDef"));
    reasons = deepCurrent(reasons);
    goal = deepCurrent(goal);
    this.queue(() => this.li.entails(deepCurrent(reasons), deepCurrent(goal)).then(cb));
  }
}

function deepCurrent<T>(x: T): T;
function deepCurrent(x: unknown): any {
  if (isDraft(x)) return current(x);
  else if (typeof x === "object" && x !== null) {
    if (Array.isArray(x)) {
      return x.map(deepCurrent);
    } else {
      return Object.fromEntries(Object.entries(x).map(([key, value]) => [key, deepCurrent(value)]));
    }
  } else return x;
}

export const LIQ = new LogicInterfaceQueue(LI);
