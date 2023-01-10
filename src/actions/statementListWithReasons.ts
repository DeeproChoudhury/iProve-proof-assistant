import { current, Draft, original } from "immer";
import { LIQ } from "../logic/LogicInterfaceQueue";
import { ActionContext, actionsWithContext } from "../store/ActionContext";
import { IProveDraft } from "../store/store";
import { Line } from "../types/AST";
import { ListField, StatementNodeData, StatementNodeType } from "../types/Node";
import { CheckStatus, Reason } from "../types/Reason";
import { mk_error, parse_error } from "../util/errors";
import { absoluteIndexToLocal, localIndexToAbsolute } from "../util/nodes";
import { statementToLine, unwrap_statements } from "../util/statements";
import * as StatementListActions from "./statementList";

type NodeAndList = {
  node: StatementNodeType;
  listField: ListField<StatementNodeData>
}

const getStatementList = (ctx: ActionContext<NodeAndList>) => {
  return ctx.draft.node.data[ctx.draft.listField];
}

const toStatementListCtx = (ctx: ActionContext<NodeAndList>) => {
  return ctx.composeLens(nal => nal.node.data[nal.listField]);
}

const shiftReasonsForNode = (
  node: Draft<StatementNodeType>,
  k: ListField<StatementNodeData>,
  index: number | undefined,
  offset: -1 | 1
) => {
  const defaultIndex = node.data[k].length;
  const changed = localIndexToAbsolute(node.data, k, index ?? defaultIndex);
  const start = Math.max(changed, node.data.givens.length); // givens don't need to be updated
  const end = node.data.givens.length + node.data.proofSteps.length + node.data.goals.length
  for (let i = start; i < end; i++) {
    const [field, relI] = absoluteIndexToLocal(node.data, i);
    const statement = node.data[field][relI];
    if (!statement.reason) continue;
    const deps = statement.reason.dependencies;
    for (let depIndex = 0; depIndex < deps.length; depIndex++) {
      if (deps[depIndex] >= changed) deps[depIndex] += offset;
    }
  }
};

const invalidateReasonForNode = (
  node: Draft<StatementNodeType>,
  k: ListField<StatementNodeData>,
  index: number
) => {
  const changed = localIndexToAbsolute(node.data, k, index);
  const start = Math.max(changed, node.data.givens.length); // givens don't need to be updated
  const end = node.data.givens.length + node.data.proofSteps.length + node.data.goals.length
  for (let i = start; i < end; i++) {
    const [field, relI] = absoluteIndexToLocal(node.data, i);
    const statement = node.data[field][relI];
    if (!statement.reason) continue;
    const deps = statement.reason.dependencies;

    if (i === changed || deps.includes(changed)) {
      statement.reason.status = "unchecked";
    }
  }
  return node;
};


export const add = (ctx: ActionContext<NodeAndList>, index?: number) => {
  shiftReasonsForNode(ctx.draft.node, ctx.draft.listField, index, 1);
  StatementListActions.add(toStatementListCtx(ctx), index);
};

export const update = (ctx: ActionContext<NodeAndList>, index: number, value: string) => {
  invalidateReasonForNode(ctx.draft.node, ctx.draft.listField, index)
  StatementListActions.update(toStatementListCtx(ctx), index, value);
};

export const remove = (ctx: ActionContext<NodeAndList>, index: number) => {
  invalidateReasonForNode(ctx.draft.node, ctx.draft.listField, index)
  shiftReasonsForNode(ctx.draft.node, ctx.draft.listField, index, -1);
  StatementListActions.remove(toStatementListCtx(ctx), index);
};

export const parse = (ctx: ActionContext<NodeAndList>, index: number) => {
  StatementListActions.parse(toStatementListCtx(ctx), index);
}

export const parseAll = (ctx: ActionContext<NodeAndList>) => {
  StatementListActions.parseAll(toStatementListCtx(ctx));
}

export const addReason = (ctx: ActionContext<NodeAndList>, index: number, reason: Reason) => {
  getStatementList(ctx)[index].reason = reason;
}

export const removeReason = (ctx: ActionContext<NodeAndList>, index: number) => {
  getStatementList(ctx)[index].reason = undefined;
}

export const updateReasonStatus = (ctx: ActionContext<NodeAndList>, index: number, status: CheckStatus) => {
  const reason = getStatementList(ctx)[index].reason;
  if (reason) reason.status = status;
}

export const checkReason = (ctx: ActionContext<NodeAndList>, index: number) => {
  const statement = getStatementList(ctx)[index];
  if (!statement.reason) return;
  const depStatements = statement.reason.dependencies.map(absIndex => {
    const [listField, relIndex] = absoluteIndexToLocal(ctx.draft.node.data, absIndex);
    return ctx.draft.node.data[listField][relIndex];
  });
  if (depStatements.some(s => !s.parsed)) {
    ctx.setError(mk_error({
      kind: "Semantic",
      msg: "Some givens have not been parsed! Exit the modal and try again"
    }));
    updateReasonStatus(ctx, index, "invalid");
    return;
  }

  if (!statement.parsed) {
    ctx.setError(mk_error({
      kind: "Semantic",
      msg: "Your objective has not been parsed! Exit the modal and try again"
    }));
    updateReasonStatus(ctx, index, "invalid");
    return;
  }

  updateReasonStatus(ctx, index, "checking");

  LIQ.queueEntails(unwrap_statements(depStatements), statementToLine(statement) as Line, ctx.newAction((ctx, verdict) => {
    switch (verdict.kind) {
      case "Valid":
        ctx.setError(undefined);
        updateReasonStatus(ctx, index, "valid");
        break;
      case "Error":
        ctx.setError(parse_error(verdict));
        updateReasonStatus(ctx, index, "invalid");
        break;
      case "Unknown":
        ctx.setError(mk_error({
          msg: "We couldn't decide whether your conclusion was true. This is either because you haven't provided enough granularity in your proof, or because your conclusion doesn't hold; try deducing more intermediate steps and supplying those as reasons, or making your conclusion more specific to the case you are working on."
        }));
        updateReasonStatus(ctx, index, "invalid");
        break;
      case "False":
        ctx.setError(mk_error({ kind: "Proof" }));
        updateReasonStatus(ctx, index, "invalid");
    }
  }));
}

const actions = {
  add, update, remove, parse, parseAll, addReason, removeReason, updateReasonStatus, checkReason
} as const;

export const makeStatementListWithReasonsActions = (set: (cb: (draft: IProveDraft) => void) => void, lens: (draft: IProveDraft) => Draft<NodeAndList>) => {
  return actionsWithContext<keyof typeof actions, NodeAndList, typeof actions>(set, actions, lens);
}

