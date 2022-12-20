import { addEdge, applyEdgeChanges, applyNodeChanges, Connection, EdgeChange, Node, NodeChange } from "reactflow";
import { ActionContext, actionsWithContext } from "../store/ActionContext";
import { IProveDraft, StoreType } from "../store/store";
import { AnyNodeType } from "../types/Node";

export const onNodesChange = ({ draft }: ActionContext<StoreType>, changes: NodeChange[]) => {
  draft.nodes = applyNodeChanges(changes, draft.nodes as Node[]) as AnyNodeType[];
};


export const onEdgesChange = ({ draft }: ActionContext<StoreType>, changes: EdgeChange[]) => {
  draft.edges = applyEdgeChanges(changes, draft.edges);
}

export const onConnect = ({ draft }: ActionContext<StoreType>, params: Connection) => {
  for (const node of draft.nodes) {
    if (node.id !== params.target) {
      continue;
    }
    node.data.edgesStatus = "unchecked";
    if (node.type === "inductionNode") {
      continue;
    }
    const source = draft.nodes.find(node => node.id === params.source);
    const sourceGoals = source && source.type !== "inductionNode" ? 
      JSON.parse(JSON.stringify(source.data.goals.filter(s => !node.data.givens.map(g => g.value).includes(s.value)).map(s => {return {...s, reason: undefined}}))) : [];
    node.data.givens = [...sourceGoals, node.data.givens];
  }

  draft.edges = addEdge({...params, 
    type:"implication", 
    id: `${params.source}-${params.target}`,
  }, draft.edges);
}

const actions = {
  onNodesChange, onEdgesChange, onConnect
} as const;

export const makeFlowActions = (set: (cb: (draft: IProveDraft) => void) => void) => {
  return actionsWithContext<keyof typeof actions, StoreType, typeof actions>(set, actions, draft => draft);
}
