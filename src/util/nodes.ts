import { SetStateAction } from "react";
import { Node } from "reactflow";
import { NodeData, StatementListFieldName } from "../types/Node";
import { StatementKind, StatementType } from "../types/Statement";
import { applyAction, Setter } from "./setters";

export function listField(k: StatementKind): StatementListFieldName {
    switch (k) {
        case "given": return "givens";
        case "proofStep": return "proofSteps";
        case "goal": return "goals";
    }
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
        [fieldName]: applyAction(action, node.data[fieldName])
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
  }
}

