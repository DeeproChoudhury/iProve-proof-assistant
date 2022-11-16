import { SetStateAction } from "react";
import { Node } from "reactflow";
import { InductionData, NodeData, StatementListFieldName } from "../types/Node";
import { StatementKind, StatementType } from "../types/Statement";
import { applyAction, Setter } from "./setters";

export function listField(k: StatementKind): StatementListFieldName {
    switch (k) {
        case "given": return "givens";
        case "proofStep": return "proofSteps";
        case "goal": return "goals";
        case "type": return "types";
        case "predicate": return "predicate";
        case "inductiveCase": return "inductiveCases";
        case "baseCase": return "baseCases";
        case "inductiveHypothesis": return "inductiveHypotheses"; 
    }
}

export function localIndexToAbsolute(data: NodeData, k: StatementKind, index: number) {
  switch (k) {
    case "given": return index;
    case "proofStep": return data.givens.length + index;
    case "goal": return data.givens.length + data.proofSteps.length + index;
  }
}

export function absoluteIndexToLocal(data: NodeData, index: number) {
  if (index < data.givens.length) return ["given", index];
  else if (index < data.givens.length + data.proofSteps.length) return ["proofStep", index - data.givens.length];
  else return ["goal", index - data.givens.length - data.proofSteps.length];
}

export const setStatementsForNode = (
  setNode: Setter<Node<NodeData>>,
  k: StatementKind
) => (
  action: SetStateAction<StatementType[]>
) => {
  setNode(node => {
    const fieldName = listField(k);
    return {
      ...node,
      data: {
        ...node.data,
        [fieldName]: applyAction(action as SetStateAction<any>, node.data[fieldName as keyof NodeData])
      }
    }
  });
};

export const setNodeWithId = (
  setNodes: Setter<Node<NodeData>[]>,
  nodeId: string
) => (action: SetStateAction<Node<NodeData>>) => {
  setNodes(nds => nds.map((nd) => nd.id === nodeId ? applyAction(action, nd) : nd));
};


export const setInductionStatementsForNode = (
  setNode: Setter<Node<InductionData>>,
  k: StatementKind
) => (
  action: SetStateAction<StatementType[]>
) => {
  setNode(node => {
    const fieldName = listField(k);
    return {
      ...node,
      data: {
        ...node.data,
        [fieldName]: applyAction(action as SetStateAction<any>, node.data[fieldName as keyof InductionData])
      }
    }
  });
};

export const setInductionNodeWithId = (
  setNodes: Setter<Node<InductionData>[]>,
  nodeId: string
) => (action: SetStateAction<Node<InductionData>>) => {
  setNodes(nds => nds.map((nd) => nd.id === nodeId ? applyAction(action, nd) : nd));
};

export const collided = (node1: Node, node2: Node): boolean => {
  const a: number = node1.position.x - node2.position.x;
  const b: number = node1.position.y - node2.position.y;
  return Math.sqrt(a * a + b * b) < 100;
}

export const getResults = (node: Node<NodeData>): StatementType[] => {
  switch (node.data.type) {
    case "given": return node.data.givens;
    case "statement": return node.data.goals;
    case "goal": return [];
    case "induction": return [];
  }
}

export const shiftReasonsForNode = (
  setNode: Setter<Node<NodeData>>
) => (
  k: "proofStep" | "goal",
  index: number | undefined,
  offset: -1 | 1
) => {
  setNode(node => {
    const {givens, proofSteps: oldProofSteps, goals: oldGoals} = node.data;
    const proofSteps = [...oldProofSteps];
    const goals = [...oldGoals];
    const defaultIndex = k === "goal" ? goals.length : proofSteps.length;
    const absI = (index ?? defaultIndex) + givens.length + (k === "goal" ? proofSteps.length : 0);
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
  setNode: Setter<Node<NodeData>>
) => (
  k: "proofStep" | "goal",
  index: number
) => {
  setNode(node => {
    const {givens, proofSteps: oldProofSteps, goals: oldGoals} = node.data;
    const proofSteps = [...oldProofSteps];
    const goals = [...oldGoals];
    const absI = index + givens.length + (k === "goal" ? proofSteps.length : 0);
    const removed = [absI];
    for (let i = absI; i < givens.length + proofSteps.length + goals.length; i++) {
      const [statements, relI] = i < givens.length + proofSteps.length ? [proofSteps, i - givens.length] : [goals, i - givens.length - proofSteps.length];
      const statement = statements[relI];
      if (!statement.reason) continue;

      const deps = statement.reason.dependencies;

      if (deps.some(x => removed.includes(x))) {
        removed.push(i);
        statements[relI] = {
          ...statement,
          reason: undefined
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
