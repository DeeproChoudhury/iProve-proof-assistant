import type { Draft } from "immer";
import { ActionContext, actionsWithContext } from "../store/ActionContext";
import { IProveDraft } from "../store/store";
import { StatementNodeType } from "../types/Node";
import { CheckStatus } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { z3Reason } from "../util/reasons";
import { isBlockEnd, isBlockStart, isTerm } from "../util/trees";
import { checkReason, updateReasonStatus } from "./statementNodeStatementList";

export const checkInternal = (ctx: ActionContext<StatementNodeType>) => {}

export const setWrappers = (ctx: ActionContext<StatementNodeType>) => {
  // sets the indentation level for each statement inside a node
  // this is run whenever the user leaves the input field of a statement and sees if 
  // any indentations can be updated (only goes through proofSteps since no indentations 
  // should be possible in givens and goals
  const wrappers = [];
  const proofSteps = ctx.draft.data.proofSteps;
  for (const step of proofSteps) {
    if (!step.parsed) continue;
    if (isBlockStart(step.parsed)) {
      // new scope so I want first line to not be wrapped in itself
      step.wrappers = [...wrappers]
      wrappers.push(step.parsed);
      continue;
    } else if (isBlockEnd(step.parsed)) {
      wrappers.pop();
    }
    step.wrappers = [...wrappers];
  }
}

export const autoAddReasons = (ctx: ActionContext<StatementNodeType>) => {
  const node = ctx.draft;
  if (node.type !== "proofNode") return node;
  const autoAddReason = (statement: Draft<StatementType>, index: number) => {
    if (
      statement.parsed
      && isTerm(statement.parsed)
      && statement.reason?.status !== "valid"
      && statement.reason?.status !== "checking"
    ) statement.reason = z3Reason([...new Array(index).keys()]);
  }
  node.data.proofSteps.forEach((statement, index) => autoAddReason(statement, index + node.data.givens.length));
  node.data.goals.forEach((statement, index) => autoAddReason(statement, index + node.data.givens.length + node.data.proofSteps.length));
}

export const recheckReasons = (ctx: ActionContext<StatementNodeType>) => {
  const node = ctx.draft;
  if (node.type !== "proofNode") return;
  for (const listField of ["proofSteps", "goals"] as const) {
    for (let i = 0; i < node.data[listField].length; i++) {
      const reason = node.data[listField][i].reason;
      if (reason && ["unchecked", "invalid"].includes(reason.status)) {
        checkReason(ctx.composeLens(node => ({ node, listField })), i);
      }
    }
  }
}

const actions = {
  checkInternal, setWrappers, autoAddReasons, recheckReasons
} as const;

export const makeStatementNodeActions = (set: (cb: (draft: IProveDraft) => void) => void, lens: (draft: IProveDraft) => Draft<StatementNodeType>) => {
  return actionsWithContext<keyof typeof actions, StatementNodeType, typeof actions>(set, actions, lens);
}

