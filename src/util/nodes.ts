import type { Draft } from "immer";
import { ActionContext } from "../store/ActionContext";
import { StatementNodeType, InductionNodeType, StatementNodeData, AnyNodeType, StatementNodeListField, AnyNodeProps } from "../types/Node";
import { CheckStatus } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { isTerm } from "./trees";

export function localIndexToAbsolute(data: StatementNodeData, k: StatementNodeListField, index: number): number {
  switch (k) {
    case "givens": return index;
    case "proofSteps": return data.givens.length + index;
    case "goals": return data.givens.length + data.proofSteps.length + index;
  }
}

export function absoluteIndexToLocal(data: StatementNodeData, index: number): [StatementNodeListField, number] {
  if (index < data.givens.length) return ["givens", index];
  else if (index < data.givens.length + data.proofSteps.length) return ["proofSteps", index - data.givens.length];
  else return ["goals", index - data.givens.length - data.proofSteps.length];
}

export const getAllStatements = (node: AnyNodeProps): StatementType[] => {
  switch (node.type) {
    case "givenNode":
    case "proofNode":
    case "goalNode":
      return [
        ...node.data.givens,
        ...node.data.proofSteps,
        ...node.data.goals
      ];
    case "inductionNode":
      return [
        ...node.data.types,
        ...node.data.motive,
        ...node.data.baseCases,
        ...node.data.inductiveCases
      ];
  }
}

export const allParsed = (node: AnyNodeProps): boolean => {
  return getAllStatements(node).every(statement => statement.parsed);
}

export const internalsStatus = (node: AnyNodeProps): CheckStatus => {
  switch (node.type) {
    case "givenNode":
    case "goalNode":
      return "valid";
    case "proofNode":
      const statements = [...node.data.proofSteps, ...node.data.goals].filter(s => s.parsed && isTerm(s.parsed));
      if (statements.some(statement => statement.reason?.status === "checking")) return "checking";
      else if (statements.some(statement => statement.reason?.status === "unchecked")) return "unchecked";
      else if (statements.every(statement => statement.reason?.status === "valid")) return "valid";
      else return "invalid";
    case "inductionNode":
      return node.data.internalsStatus;
  }
}

export const edgesStatus = (node: AnyNodeProps): CheckStatus => {
  switch (node.type) {
    case "givenNode":
      return "valid";
    default:
      return node.data.edgesStatus;
  }
}

export const isInductionNode = (node: AnyNodeType): node is InductionNodeType => {
  return node.type === "inductionNode";
}

export const isStatementNode = (node: AnyNodeType): node is StatementNodeType => {
  return node.type !== "inductionNode";
}

export const getInputs = (node: AnyNodeType): StatementType[] => {
  switch (node.type) {
    case "givenNode":
      return [];
    case "proofNode":
    case "goalNode":
      return node.data.givens;
    case "inductionNode":
      return node.data.baseCases.concat(node.data.inductiveCases);
  }
}

export const getOutputs = (node: AnyNodeType): StatementType[] => {
  switch (node.type) {
    case "givenNode":
    case "proofNode":
      return node.data.goals;
    case "goalNode":
      return [];
    case "inductionNode":
      return node.data.motive;
  }
}

export const narrowNodeCtx = (ctx: ActionContext<AnyNodeType>) => {
  const ctxStatementNode = ctx.narrowType((node): node is Draft<StatementNodeType>  => node.type !== "inductionNode")
  if (ctxStatementNode) {
    return {
      kind: "statementNode",
      ctx: ctxStatementNode
    } as const;
  }

  const ctxInductionNode = ctx.narrowType((node): node is Draft<InductionNodeType>  => node.type === "inductionNode")
  if (ctxInductionNode) {
    return {
      kind: "inductionNode",
      ctx: ctxInductionNode
    } as const;
  }

  throw new Error("impossible node type (unreachable)");
}
