import type { Draft } from "immer";
import { ActionContext, actionsWithContext } from "../store/ActionContext";
import { IProveDraft } from "../store/store";
import { InductionNodeType } from "../types/Node";

export const invalidateInternals = (ctx: ActionContext<InductionNodeType>) => {
  ctx.draft.data.internalsStatus = "unchecked";
}

const actions = {
  invalidateInternals
} as const;

export const makeInductionNodeActions = (set: (cb: (draft: IProveDraft) => void) => void, lens: (draft: IProveDraft) => Draft<InductionNodeType>) => {
  return actionsWithContext<keyof typeof actions, InductionNodeType, typeof actions>(set, actions, lens);
}

