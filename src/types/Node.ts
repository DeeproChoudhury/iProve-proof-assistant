import { MutableRefObject } from "react";
import { InductionNodeCallbacks } from "../callbacks/inductionNodeCallbacks";
import { NodeCallbacks } from "../callbacks/nodeCallbacks";
import { StatementType } from "./Statement";

export type NodeType = "statement" | "given" | "goal" | "induction" ;

export type GeneralNodeData = Readonly<{
  label: string;
  id: number;
  type: NodeType;
  declarationsRef: MutableRefObject<StatementType[]>;
  correctImplication?: boolean;
}>;

export type NodeData = GeneralNodeData & Readonly<{
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  thisNode: NodeCallbacks;
}>;

export type InductionData = GeneralNodeData & Readonly<{
  typeDeclarationsRef: MutableRefObject<StatementType[]>;
  types: StatementType[];
  predicate: StatementType[];
  inductiveCases: StatementType[];
  baseCases: StatementType[];
  inductiveHypotheses: StatementType[];
  thisNode: InductionNodeCallbacks;
}>; 

export type ListField<T extends NodeData | InductionData> = T extends NodeData ? ("givens" | "proofSteps" | "goals") : T extends InductionData ? ("types" | "predicate" | "inductiveCases" | "baseCases" | "inductiveHypotheses") : never

export type AnyNodeData = NodeData | InductionData;
