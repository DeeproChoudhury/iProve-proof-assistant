import type { Draft } from "immer";
import { IProveDraft } from '../store/store';
import { AnyNodeType, ListField } from '../types/Node';
import { StatementType } from "../types/Statement";

export const getNodeOrThrow = (draft: IProveDraft, nodeId: string): Draft<AnyNodeType> => {
  const node = draft.nodes.find(node => node.id === nodeId);
  if (!node)
    throw new Error(`Tried to invoke action for node ${nodeId}, but it does not exist`);
  return node;
};

export const isListFieldOf = <T extends AnyNodeType>(node: T, listField: string): listField is ListField<T["data"]> => {

  if (node.type === "inductionNode") {
    if (listField === "types"
      || listField === "motive"
      || listField === "inductiveCases"
      || listField === "baseCases"
      || listField === "identifier"
    ) {
      return true;
    }
  } else {
    if (listField === "givens"
      || listField === "proofSteps"
      || listField === "goals"
    ) {
      return true;
    }
  }
  return false;
}

export const getStatementsOrThrow = (node: AnyNodeType, listField: string): Draft<StatementType[]> => {
  if (node.type === "inductionNode") {
    if (listField === "types"
      || listField === "motive"
      || listField === "inductiveCases"
      || listField === "baseCases"
      || listField === "identifier"
    ) {
      return node.data[listField];
    }
  } else {
    if (listField === "givens"
      || listField === "proofSteps"
      || listField === "goals"
    ) {
      return node.data[listField]
    }
  }
  throw new Error(`Node kind ${node.type} does not have a statement list called ${listField}`);
};
