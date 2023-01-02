import type { Draft } from "immer";
import evaluate from "../logic/Parser";
import { ActionContext, ActionRecord, actionsWithContext, RemoveFirstArg } from "../store/ActionContext";
import { IProveDraft } from "../store/store";
import { Line } from "../types/AST";
import { StatementType } from "../types/Statement";
import { mk_error } from "../util/errors";

const updateWithParsed = (ctx: ActionContext<StatementType[]>, index: number) => {
  const statement = ctx.draft[index];
  const parsedOrError = evaluate(statement.value);
  if(parsedOrError.kind === "Error") {
    statement.syntaxCorrect = false;
    ctx.setError(mk_error({
      kind: "Syntax", statement: statement, column: parsedOrError.pos?.columnBegin,
      msg: parsedOrError.message
        .replace("token: <END-OF-FILE>", "entire input")
    }));
  } else {
    // console.log(parsedOrError);
    statement.parsed = parsedOrError as Line; // TODO: avoid cast here?
    statement.syntaxCorrect = true;
  }
  return statement;
}

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

export const parse = (ctx: ActionContext<StatementType[]>, index: number) => {
  ctx.draft[index] = updateWithParsed(ctx, index);
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
