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
  types: StatementType[];
  predicate: StatementType[];
  inductiveCase: StatementType[];
  baseCases: StatementType[];
  inductiveHypotheses: StatementType[];
  thisNode: InductionNodeCallbacks;
}>; 

export type StatementListFieldName = "givens" | "proofSteps" | "goals" | "types" | "baseCases" | "inductiveCase" | "predicate" | "inductiveHypotheses";
