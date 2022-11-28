import { SetStateAction } from "react";
import { Node } from "reactflow";
import { ListField, StatementNodeType, InductionNodeType, StatementNodeData } from "../types/Node";
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
  k: "proofSteps" | "goals",
  index: number | undefined,
  offset: -1 | 1
) => {
  setNode(node => {
    const {givens, proofSteps: oldProofSteps, goals: oldGoals} = node.data;
    const proofSteps = [...oldProofSteps];
    const goals = [...oldGoals];
    const defaultIndex = k === "goals" ? goals.length : proofSteps.length;
    const absI = (index ?? defaultIndex) + givens.length + (k === "goals" ? proofSteps.length : 0);
    let start = absI;
    for (let i = start; i < givens.length + proofSteps.length + goals.length; i++) {
      const [statements, relI] = i < givens.length + proofSteps.length ? [proofSteps, i - givens.length] : [goals, i - givens.length - proofSteps.length];
      const statement = statements[relI];
      if (!statement.reason) continue;
      const newDeps = [...statement.reason.dependencies];
      for (let depIndex = 0; depIndex < newDeps.length; depIndex++) {
        if (newDeps[depIndex] >= start) newDeps[depIndex] += offset;
      }
      statements[relI] = {
        ...statement,
        reason: {
          ...statement.reason,
          dependencies: newDeps
        }
      }
    }
    return {
      ...node,
      data: {
        ...node.data,
        proofSteps,
        goals
      }
    }
  });
};

export const invalidateReasonForNode = (
  setNode: Setter<StatementNodeType>
) => (
  k: "proofSteps" | "goals",
  index: number
) => {
  setNode(node => {
    const {givens, proofSteps: oldProofSteps, goals: oldGoals} = node.data;
    const proofSteps = [...oldProofSteps];
    const goals = [...oldGoals];
    const absI = index + givens.length + (k === "goals" ? proofSteps.length : 0);
    for (let i = absI; i < givens.length + proofSteps.length + goals.length; i++) {
      const [statements, relI] = i < givens.length + proofSteps.length ? [proofSteps, i - givens.length] : [goals, i - givens.length - proofSteps.length];
      const statement = statements[relI];
      if (!statement.reason) continue;
      const deps = statement.reason.dependencies;

      if (relI === index || deps.includes(absI)) {
        statements[relI] = {
          ...statement,
          reason: {
            ...statement.reason,
            status: "unchecked"
          }
        }
      }
    }
    return {
      ...node,
      data: {
        ...node.data,
        proofSteps,
        goals
      }
    }
  });
};
