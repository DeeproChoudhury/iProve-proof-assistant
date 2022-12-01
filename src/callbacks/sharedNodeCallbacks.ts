import { AnyNodeType } from "../types/Node"
import { setNodeWithId } from "../util/nodes";
import { Setter } from "../util/setters"


export const makeSharedNodeCallbacks = <T extends AnyNodeType>(setNodes: Setter<AnyNodeType[]>, nodePredicate: (node: AnyNodeType) => node is T, nodeId: string) => {
  const setNode = setNodeWithId(setNodes, nodePredicate, nodeId);
  return {
    delete: (): void => setNodes(nds => nds.filter(nd => nd.id !== nodeId)),
    invalidateEdges: () => setNode(node => ({...node, data: {...node.data, edgesStatus: "unchecked"}})),
    invalidateOutgoingEdges: () => {} // TODO
  } 
}
