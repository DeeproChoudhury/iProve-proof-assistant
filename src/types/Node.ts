import { Node, NodeProps } from "reactflow";
import { CheckStatus } from "./Reason";
import { StatementType } from "./Statement";

export type NodeKind = "proofNode" | "givenNode" | "goalNode" | "inductionNode";
export type StatementNodeListField = "givens" | "proofSteps" | "goals";
export type InductionNodeListField = "types" | "inductiveCases" | "baseCases" | "motive" | "identifier";

export type ListField<T extends NodeKind = NodeKind> = 
  T extends "inductionNode" ? InductionNodeListField
  : StatementNodeListField;

type SharedNodeData = {
  label: string;
  edgesStatus: CheckStatus;
}

export type StatementNodeData = SharedNodeData & Record<ListField<"proofNode">, StatementType[]>;

export type InductionNodeData = SharedNodeData
  & { internalsStatus: CheckStatus; } 
  & Record<ListField<"inductionNode">, StatementType[]>; 

export type ProofNodeType = Node<StatementNodeData> & { type: "proofNode" };
export type GivenNodeType = Node<StatementNodeData> & { type: "givenNode" };
export type GoalNodeType = Node<StatementNodeData> & { type: "goalNode" };
export type StatementNodeType = ProofNodeType | GivenNodeType | GoalNodeType;
export type InductionNodeType = Node<InductionNodeData> & { type: "inductionNode" };
export type AnyNodeType = StatementNodeType | InductionNodeType;

export type AnyNodeProps = { type: "inductionNode", data: InductionNodeData } | {type: "givenNode" | "proofNode" | "goalNode", data: StatementNodeData};
