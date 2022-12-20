import type { Draft } from "immer";
import { ActionContext, ActionRecord, actionsWithContext, RemoveFirstArg } from "../store/ActionContext";
import { IProveDraft } from "../store/store";
import { StatementType } from "../types/Statement";
import { updateWithParsed } from "../util/statements";

export const add = ({ draft }: ActionContext<StatementType[]>, index?: number) => {
  draft.splice(index ?? draft.length, 0, { value: "", wrappers: [] })
};

export const update = ({ draft }: ActionContext<StatementType[]>, index: number, statementValue: string) => {
  draft[index].value = statementValue;
  draft[index].parsed = undefined;
}

export const remove = ({ draft }: ActionContext<StatementType[]>, index: number) => {
  draft.splice(index, 1);
};

export const parse = ({ draft, setError }: ActionContext<StatementType[]>, index: number) => {
  draft[index] = updateWithParsed(setError)(draft[index]);
};

export const parseAll = (ctx: ActionContext<StatementType[]>) => {
  for (let i = 0; i < ctx.draft.length; i++) parse(ctx, i);
};

export const updateWithStatement = ({ draft }: ActionContext<StatementType[]>, index: number, statement: StatementType) => {
  draft[index] = statement;
};

const actions = {
  add, update, remove, parse, parseAll, updateWithStatement
} as const;

export const makeStatementListActions = (set: (cb: (draft: IProveDraft) => void) => void, lens: (draft: IProveDraft) => Draft<StatementType[]>) => {
  return actionsWithContext<keyof typeof actions, StatementType[], typeof actions>(set, actions, lens);
}
