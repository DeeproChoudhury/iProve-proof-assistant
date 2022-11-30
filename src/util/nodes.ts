import { SetStateAction } from "react";
import { Node } from "reactflow";
import { ListField, StatementNodeType, InductionNodeType, StatementNodeData, AnyNodeType, AnyNodeProps } from "../types/Node";
import { CheckStatus } from "../types/Reason";
import { StatementType } from "../types/Statement";
import { applyAction, Setter } from "./setters";

export function localIndexToAbsolute(data: StatementNodeData, k: ListField<StatementNodeData>, index: number): number {
  switch (k) {
    case "givens": return index;
    case "proofSteps": return data.givens.length + index;
    case "goals": return data.givens.length + data.proofSteps.length + index;
  }
}

export function absoluteIndexToLocal(data: StatementNodeData, index: number): [ListField<StatementNodeData>, number] {
  if (index < data.givens.length) return ["givens", index];
  else if (index < data.givens.length + data.proofSteps.length) return ["proofSteps", index - data.givens.length];
  else return ["goals", index - data.givens.length - data.proofSteps.length];
}

export const setStatementsForNode = <K extends string, D extends Record<K, StatementType[]>, T extends Node<D>>(
  setNode: Setter<T>,
  k: K
) => (
  action: SetStateAction<StatementType[]>
) => {
  setNode(node => {
    return {
      ...node,
      data: {
        ...node.data,
        [k]: applyAction(action, node.data[k])
      }
    }
  });
};

export const setNodeWithId = <T extends StatementNodeType | InductionNodeType>(
  setNodes: Setter<T[]>,
  nodeId: string
) => (action: SetStateAction<T>) => {
  setNodes(nds => nds.map((nd) => nd.id === nodeId ? applyAction(action, nd) : nd));
};

export const collided = (node1: Node, node2: Node): boolean => {
  const a: number = node1.position.x - node2.position.x;
  const b: number = node1.position.y - node2.position.y;
  return Math.sqrt(a * a + b * b) < 100;
}

export const shiftReasonsForNode = (
  setNode: Setter<StatementNodeType>
) => (
  k: ListField<StatementNodeData>,
  index: number | undefined,
  offset: -1 | 1
) => {
  setNode(node => {
    const newNode = {
      ...node,
      data: {
        ...node.data,
        proofSteps: [...node.data.proofSteps],
        goals: [...node.data.goals]
      }
    }

    const defaultIndex = node.data[k].length;
    const changed = localIndexToAbsolute(node.data, k, index ?? defaultIndex);
    const start = Math.max(changed, newNode.data.givens.length); // givens don't need to be updated
    const end = newNode.data.givens.length + newNode.data.proofSteps.length + newNode.data.goals.length
    for (let i = start; i < end; i++) {
      const [field, relI] = absoluteIndexToLocal(newNode.data, i);
      const statement = newNode.data[field][relI];
      if (!statement.reason) continue;
      const newDeps = [...statement.reason.dependencies];
      for (let depIndex = 0; depIndex < newDeps.length; depIndex++) {
        if (newDeps[depIndex] >= changed) newDeps[depIndex] += offset;
      }
      newNode.data[field][relI] = {
        ...statement,
        reason: {
          ...statement.reason,
          dependencies: newDeps
        }
      }
    }
    return newNode;
  });
};

export const invalidateReasonForNode = (
  setNode: Setter<StatementNodeType>
) => (
  k: ListField<StatementNodeData>,
  index: number
) => {
  setNode(node => {
    const newNode = {
      ...node,
      data: {
        ...node.data,
        proofSteps: [...node.data.proofSteps],
        goals: [...node.data.goals]
      }
    }
    const changed = localIndexToAbsolute(newNode.data, k, index);
    const start = Math.max(changed, newNode.data.givens.length); // givens don't need to be updated
    const end = newNode.data.givens.length + newNode.data.proofSteps.length + newNode.data.goals.length
    for (let i = start; i < end; i++) {
      const [field, relI] = absoluteIndexToLocal(newNode.data, i);
      const statement = newNode.data[field][relI];
      if (!statement.reason) continue;
      const deps = statement.reason.dependencies;

      if (i === changed || deps.includes(changed)) {
        newNode.data[field][relI] = {
          ...statement,
          reason: {
            ...statement.reason,
            status: "unchecked"
          }
        }
      }
    }
    return newNode;
  });
};

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
    case "proofNode":
      return "valid";
    case "goalNode":
      const statements = [...node.data.proofSteps, ...node.data.goals];
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
