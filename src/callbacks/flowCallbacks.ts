import { MutableRefObject } from "react";
import { Edge, NodeChange, applyNodeChanges, EdgeChange, applyEdgeChanges, Connection, addEdge, Node } from "reactflow";
import { InductionNodeType, StatementNodeType } from "../types/Node";
import { StatementType } from "../types/Statement";
import { collided } from "../util/nodes";
import { Setter } from "../util/setters";
import { NodeCallbacks } from "./nodeCallbacks";

export const makeFlowCallbacks = (nodes: StatementNodeType[], inductionNodes: InductionNodeType[], setNodes: Setter<StatementNodeType[]>, setInductionNodes: Setter<InductionNodeType[]>, setEdges: Setter<Edge[]>, declarationsRef: MutableRefObject<StatementType[]>, nextId: () => number, makeThisNode: (id: string) => NodeCallbacks) => ({
  onNodeDragStop: (event: React.MouseEvent, node: Node, selectedNodes: Node[]) => {
    if (node.data.type !== 'statement') return;

    const other: StatementNodeType | undefined = nodes
      .filter((other) => other.type === 'proofNode')
      .find((other) => other.id !== node.id && collided(node, other));

    if (!other) return;

    const [first, second] = node.position.y < other.position.y ? [node, other] : [other, node];
    const count = nextId();
    setNodes(nds => [...nds.filter(n => n.id !== node.id && n.id !== other.id), {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        edgesStatus: "unchecked",
        givens: first.data.givens,
        proofSteps: [
          ...first.data.proofSteps,
          ...first.data.goals,
          ...second.data.givens,
          ...second.data.proofSteps
        ],
        goals: second.data.goals,
        declarationsRef,
        thisNode: makeThisNode(`${count}`)
      },
      position: { x: other.position.x, y: other.position.y },
      type: 'proofNode',
    }]);
  },
  onNodesChange: (changes: NodeChange[]) => {
    setNodes((nds) => applyNodeChanges(changes, nds) as StatementNodeType[]);
    setInductionNodes((nds) => applyNodeChanges(changes, nds) as InductionNodeType[]);
  },
  onEdgesChange: (changes: EdgeChange[]) => setEdges((eds) => applyEdgeChanges(changes, eds)),
  onConnect: (params: Connection) => {
    const sourceGoals = nodes.find(node => node.id === params.source)?.data.goals || [];
    setNodes(nds => nds.map((node) => {
      if (node.id !== params.target) {
        return node;
      }
      return {...node, data: {...node.data, edgesStatus: "unchecked", givens: [...node.data.givens, ...sourceGoals]}};
    }));
    setEdges((eds) => addEdge({...params, 
      type:"implication", 
      id: `${params.source}-${params.target}`,
    }, eds));
  }
  // onKeyDown: useCallback(() => {})
});

export type FlowCallbacks = ReturnType<typeof makeFlowCallbacks>;
