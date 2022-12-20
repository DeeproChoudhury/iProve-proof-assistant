import { current, isDraft } from "immer";
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
    if (isDraft(reasons)) reasons = current(reasons);
    if (isDraft(goal)) goal = current(goal);
    this.queue(() => this.li.entails(reasons, goal).then(cb));
  }
}

export const LIQ = new LogicInterfaceQueue(LI);
