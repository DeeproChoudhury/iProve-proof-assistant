import { MutableRefObject } from "react";
import { Node } from "reactflow";
import { InductionNodeCallbacks } from "../callbacks/inductionNodeCallbacks";
import { NodeCallbacks } from "../callbacks/nodeCallbacks";
import { Variable } from "./AST";
import { CheckStatus } from "./Reason";
import { StatementType } from "./Statement";

export type NodeType = "proofNode" | "givenNode" | "goalNode" | "inductionNode";

export type StatementNodeData = {
  label: string;
  declarationsRef: MutableRefObject<StatementType[]>;
  correctImplication?: CheckStatus;
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  parsed?: boolean;
  thisNode: NodeCallbacks;
};

export type InductionNodeData = {
  label: string;
  declarationsRef: MutableRefObject<StatementType[]>;
  correctImplication?: CheckStatus;
  typeDeclarationsRef: MutableRefObject<StatementType[]>;
  types: StatementType[];
  thisNode: InductionNodeCallbacks;

  inductiveCases: StatementType[];
  baseCases: StatementType[];
  motive: StatementType[];
}; 

export type ListField<T extends StatementNodeData | InductionNodeData> = T extends StatementNodeData ? ("givens" | "proofSteps" | "goals") : T extends InductionNodeData ? ("types" | "inductiveCases" | "baseCases" | "motive") : never

export type AnyNodeData = StatementNodeData | InductionNodeData;

export type ProofNodeType = Node<StatementNodeData> & { type: "proofNode" };
export type GivenNodeType = Node<StatementNodeData> & { type: "givenNode" };
export type GoalNodeType = Node<StatementNodeData> & { type: "goalNode" };
export type StatementNodeType = ProofNodeType | GivenNodeType | GoalNodeType;
export type InductionNodeType = Node<InductionNodeData> & { type: "inductionNode" };
