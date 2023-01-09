import { StoreType } from "../store/store"

export type ExportedProof = {
  nodes: StoreType["nodes"];
  edges: StoreType["edges"];
  declarations: StoreType["declarations"];
  types: StoreType["typeDeclarations"];
  nextNodeId: number;
}
