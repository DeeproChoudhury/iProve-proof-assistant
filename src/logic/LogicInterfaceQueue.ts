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
    this.queue(() => this.li.entails(reasons, goal).then(cb));
  }
}

export const LIQ = new LogicInterfaceQueue(LI);
