import { useState, useCallback } from 'react';
import ReactFlow, {
  Controls,
  Background,
  applyNodeChanges,
  applyEdgeChanges,
  addEdge,
  Node,
  Edge,
  NodeChange, 
  EdgeChange,
  Connection,
} from 'reactflow';
import 'reactflow/dist/style.css';
import { getPositionOfLineAndCharacter } from 'typescript';
import TextUpdaterNode from './TextUpdaterNode';

import './TextUpdaterNode.css';
const initialNodes: Node[] = [];

const initialEdges: Edge[] = [];
const nodeTypes = { textUpdater: TextUpdaterNode };

function Flow() {
  const [nodes, setNodes] = useState(initialNodes);
  const [edges, setEdges] = useState(initialEdges);
  const [count, setCount] = useState(0);
  const onNodesChange = useCallback(
    (changes: NodeChange[]) => setNodes((nds) => applyNodeChanges(changes, nds)),
    []
  );
  const onEdgesChange = useCallback(
    (changes: EdgeChange[]) => setEdges((eds) => applyEdgeChanges(changes, eds)),
    []
  );

  const onConnect = useCallback((params: Connection) => setEdges((eds) => addEdge(params, eds)), []);

  const deleteNodeById = (id: string) => {
    setNodes(nds => nds.filter(node => node.id !== id));
  };

  const collided = (node1: Node, node2: Node): boolean => {
    const a: number = node1.position.x - node2.position.x;
    const b: number = node1.position.y - node2.position.y; 
    return Math.sqrt(a * a + b * b) < 100;
  }

  const onNodeDragStop = useCallback((event: React.MouseEvent, node: Node, selectedNodes: Node[]) => {
    // probably also need to check node type here
    // I don't think we want to merge givens or goals with anything
    const other: Node<any> | undefined = nodes.find((other) => other.id !== node.id && collided(node, other));
    if (other !== undefined) {
      setNodes(nds => nds.filter(n => n.id !== node.id && n.id !== other.id));
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {label: `Node ${count}`, delete: deleteNodeById, id: count, type: 'statement'},
        position: { x: node.position.x, y: node.position.y },
        type: 'textUpdater',
      }]);
      setCount(count + 1);
    }
  }, [nodes]);

  const background = <Background />;

  return (
    <div>
      <div>
        <button onClick={() => {
          setNodes([...nodes, {
            id: `${count}`,
            data: {label: `Node ${count}`, delete: deleteNodeById, id: count, type: 'statement'},
            position: { x: 300, y: 0 },
            type: 'textUpdater',
          }]);
          setCount(count + 1)}}>Add Node</button>
        
        <button onClick={() => {
          setNodes([...nodes, {
            id: `${count}`,
            data: {label: `Node ${count}`, delete: deleteNodeById, id: count, type: 'given'},
            position: { x: 300, y: 0 },
            type: 'textUpdater',
          }]);
          setCount(count + 1)}}>Add Given</button>
        
        <button onClick={() => {
          setNodes([...nodes, {
            id: `${count}`,
            data: {label: `Node ${count}`, delete: deleteNodeById, id: count, type: 'goal'},
            position: { x: 300, y: 0 },
            type: 'textUpdater',
          }]);
          setCount(count + 1)}}>Add Goal</button>
      </div>
    <div  style={{ height: '450px', width: '100%'}}>
      <ReactFlow
        nodes={nodes}
        nodeTypes={nodeTypes}
        onNodesChange={onNodesChange}
        edges={edges}
        onEdgesChange={onEdgesChange}
        onConnect={onConnect}
        onNodeDragStop={onNodeDragStop}
      >
        {background}
        <Controls />
      </ReactFlow>
    </div>
    </div>
  );
}

export default Flow;
