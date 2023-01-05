import { useMemo } from "react";
import { useIProveStore } from "./store";

export const useStatementNodeActions = (nodeId: string) => {
  const deleteNode = useIProveStore(store => store.actions.global.deleteNode);
  const forStatementNode = useIProveStore(store => store.actions.forStatementNode);
  return useMemo(() => ({
    deleteNode: () => deleteNode(nodeId),
    ...forStatementNode(nodeId)
  }), [deleteNode, forStatementNode]);
}

export const useInductionNodeActions = (nodeId: string) => {
  const deleteNode = useIProveStore(store => store.actions.global.deleteNode);
  const forInductionNode = useIProveStore(store => store.actions.forInductionNode);
  return useMemo(() => ({
    deleteNode: () => deleteNode(nodeId),
    ...forInductionNode(nodeId)
  }), [deleteNode, forInductionNode]);
}
