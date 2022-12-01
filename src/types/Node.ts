import { MutableRefObject } from "react";
import { Node } from "reactflow";
import { StatementListCallbacks } from "../callbacks/statementListCallbacks";
import { CheckStatus } from "./Reason";
import { StatementType } from "./Statement";

export type NodeKind = "proofNode" | "givenNode" | "goalNode" | "inductionNode";

type SharedNodeData = {
  label: string;
  edgesStatus: CheckStatus;
  declarationsRef: MutableRefObject<StatementType[]>;
  typeDeclarationsRef: MutableRefObject<StatementType[]>;
}

type SharedNodeCallbacks = {
  delete: () => void;
  parseAll: () => void;
  checkInternal: () => void;
  checkEdges: () => void;
  invalidateEdges: () => void;
  invalidateOutgoingEdges: () => void;
}

export type StatementNodeData = SharedNodeData & {
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  thisNode: SharedNodeCallbacks & {
    givens: StatementListCallbacks;
    proofSteps: StatementListCallbacks;
    goals: StatementListCallbacks;
    setWrappers: () => void;
    autoAddReasons: () => void;
  };
};

export type InductionNodeData = SharedNodeData & {
  internalsStatus: CheckStatus;
  types: StatementType[];
  motive: StatementType[];
  inductiveCases: StatementType[];
  baseCases: StatementType[];
  thisNode: SharedNodeCallbacks & {
    types: StatementListCallbacks;
    motive: StatementListCallbacks;
    baseCases: StatementListCallbacks;
    inductiveCases: StatementListCallbacks;
    invalidateInternals: () => void;
  }
}; 

export type ListField<T extends StatementNodeData | InductionNodeData> = T extends StatementNodeData ? ("givens" | "proofSteps" | "goals") : T extends InductionNodeData ? ("types" | "inductiveCases" | "baseCases" | "motive") : never

export type AnyNodeData = StatementNodeData | InductionNodeData;

export type ProofNodeType = Node<StatementNodeData> & { type: "proofNode" };
export type GivenNodeType = Node<StatementNodeData> & { type: "givenNode" };
export type GoalNodeType = Node<StatementNodeData> & { type: "goalNode" };
export type StatementNodeType = ProofNodeType | GivenNodeType | GoalNodeType;
export type InductionNodeType = Node<InductionNodeData> & { type: "inductionNode" };
export type AnyNodeType = StatementNodeType | InductionNodeType;

export type ProofNodeProps = { type: "proofNode", data: StatementNodeData };
export type GivenNodeProps = { type: "givenNode", data: StatementNodeData };
export type GoalNodeProps = { type: "goalNode", data: StatementNodeData };
export type InductionNodeProps = { type: "inductionNode", data: InductionNodeData };
export type AnyNodeProps = ProofNodeProps | GivenNodeProps | GoalNodeProps | InductionNodeProps;
