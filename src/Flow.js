import { useState, useCallback } from 'react';
import ReactFlow, {
  Controls,
  Background,
  applyNodeChanges,
  applyEdgeChanges,
  addEdge,
} from 'reactflow';
import 'reactflow/dist/style.css';
import TextUpdaterNode from './TextUpdaterNode.js';

import './TextUpdaterNode.css';
const initialNodes = [];

const initialEdges = [];
const nodeTypes = { textUpdater: TextUpdaterNode };

function Flow() {
  const [nodes, setNodes] = useState(initialNodes);
  const [edges, setEdges] = useState(initialEdges);
  const [count, setCount] = useState(0);
  const onNodesChange = useCallback(
    (changes) => setNodes((nds) => applyNodeChanges(changes, nds)),
    []
  );
  const onEdgesChange = useCallback(
    (changes) => setEdges((eds) => applyEdgeChanges(changes, eds)),
    []
  );

  const onConnect = useCallback((params) => setEdges((eds) => addEdge(params, eds)), []);

  const deleteNodeById = (id) => {
    setNodes(nds => nds.filter(node => node.id !== id));
  };

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
      >
        <Background />
        <Controls />
      </ReactFlow>
    </div>
    </div>
  );
}

export default Flow;
