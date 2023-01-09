import { StoreType } from "../store/store"
import { AnyNodeType, GivenNodeType, GoalNodeType, InductionNodeType, ProofNodeType } from "./Node";

type ExportedNodeType<T extends AnyNodeType> = Pick<T, "id" | "type" | "position" | "data">[]

export type ExportedProof = {
  nodes: ExportedNodeType<GivenNodeType> | ExportedNodeType<ProofNodeType> | ExportedNodeType<GoalNodeType> | ExportedNodeType<InductionNodeType>;
  edges: StoreType["edges"];
  declarations: StoreType["declarations"];
  types: StoreType["typeDeclarations"];
  nextNodeId: number;
}
