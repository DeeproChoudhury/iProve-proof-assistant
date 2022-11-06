import { MutableRefObject } from "react";
import { NodeCallbacks } from "../callbacks/nodeCallbacks";
import { StatementType } from "./Statement";

export type NodeType = "statement" | "given" | "goal";

export type NodeData = Readonly<{
  label: string;
  id: number;
  type: NodeType;
  givens: StatementType[];
  proofSteps: StatementType[];
  goals: StatementType[];
  declarationsRef: MutableRefObject<StatementType[]>;
  correctImplication?: boolean;
  thisNode: NodeCallbacks
}>;

export type StatementListFieldName = "givens" | "proofSteps" | "goals";
