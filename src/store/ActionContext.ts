import type { Draft } from "immer";
import { IProveError } from "../types/ErrorLocation";
import { IProveDraft } from "./store";

// Information passed to an action that operates on a T
export class ActionContext<T> {
  #set: (cb: (draft: IProveDraft) => void) => void; // the set function from the store
  #draft: IProveDraft; // the current draft
  #lens: (draft: IProveDraft) => Draft<T>; // extract T from the draft
  draft: Draft<T>;

  constructor(set: (cb: (draft: IProveDraft) => void) => void, draft: IProveDraft, lens: (draft: IProveDraft) => Draft<T>) {
    this.#set = set;
    this.#draft = draft;
    this.#lens = lens;
    this.draft = this.#lens(this.#draft);
  }

  // this is a separate function as it is the only piece of state that is modified
  // non-locally
  setError(error: IProveError | undefined): void {
    this.#draft.error = error;
  }

  narrowType<S extends T>(guard: (current: Draft<T>) => current is Draft<S>): ActionContext<S> | undefined {
    if (!guard(this.draft)) return undefined;
    else return this as unknown as ActionContext<S>;
  }

  composeLens<S>(lens: (draft: Draft<T>) => Draft<S>) {
    return new ActionContext<S>(this.#set, this.#draft, baseDraft => (lens(this.#lens(baseDraft))));
  }

  replaceLens<S>(lens: (draft: IProveDraft) => Draft<S>) {
    return new ActionContext<S>(this.#set, this.#draft, lens);
  }

  // create a new action function that can safely be passed into a callback/promise
  // and called later
  newAction<Args extends any[]>(action: (ctx: ActionContext<T>, ...args: Args) => void): ((...args: Args) => void) {
    return actionWithContext(this.#set, this.#lens, action);
  }
}

export type ActionRecord<K extends string, A> = Record<K, (arg1: A, ...args: any[]) => void>;

export type RemoveFirstArg<D extends ActionRecord<any, any>> = D extends ActionRecord<infer K, infer T> ? {
  [Key in K]: D[Key] extends (arg1: T, ...args: infer Args) => void ? (...args: Args) => void : never;
} : never;

const removeFirstArg = <K extends string, A, T extends ActionRecord<K, A>>(actions: T, argRemover: <Args extends any[]>(action: (arg1: A, ...args: Args) => void) => (...args: Args) => void): RemoveFirstArg<T> => {
  const res: any = {};
  for (const key in actions) {
    res[key] = argRemover(actions[key]);
  }
  return res;
}

export const actionWithContext = <T, Args extends any[]>(
  set: (cb: (draft: IProveDraft) => void) => void,
  lens: (draft: IProveDraft) => Draft<T>,
  action: (ctx: ActionContext<T>, ...args: Args) => void
) => (...args: Args): void => set(draft => action(new ActionContext(set, draft, lens), ...args));

export const actionsWithContext = <
  K extends string, // names of actions
  T, // common type to operate on
  D extends ActionRecord<K, ActionContext<T>> // exact type of actions
>(
  set: (cb: (draft: IProveDraft) => void) => void,
  actions: D,
  lens: (draft: IProveDraft) => Draft<T>
): RemoveFirstArg<D> => {
  return removeFirstArg<K, ActionContext<T>, D>(actions, action => actionWithContext(set, lens, action))
}
