import { useState, useCallback } from 'react';
import { Button, Stack } from '@chakra-ui/react'
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

  const updateStatements = (nodeId: string, statementIndex: number, statement: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        const newStatements = node.data.statements;
        newStatements[statementIndex].value = statement;
        node.data = {
          ...node.data,
          statements: newStatements,
        };
      }
      return node;
    }));
  };

  const addGiven = (nodeId: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        node.data = {
          ...node.data,
          statements: [...node.data.statements, { value: '', isGiven: true }],
        };
      }
      return node;
    }));
  }

  const addProofStep = (nodeId: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        node.data = {
          ...node.data,
          statements: [...node.data.statements, { value: '', isGiven: false }],
        };
      }
      return node;
    }));
  }

  const collided = (node1: Node, node2: Node): boolean => {
    const a: number = node1.position.x - node2.position.x;
    const b: number = node1.position.y - node2.position.y;
    return Math.sqrt(a * a + b * b) < 100;
  }

  const onNodeDragStop = useCallback((event: React.MouseEvent, node: Node, selectedNodes: Node[]) => {
    // probably also need to check node type here
    // I don't think we want to merge givens or goals with anything
    if (node.data.type !== 'statement') {
      return;
    }
    const other: Node<any> | undefined =
      nodes.filter((other) => other.data.type === 'statement')
        .find((other) => other.id !== node.id && collided(node, other));
    if (other !== undefined) {
      setNodes(nds => nds.filter(n => n.id !== node.id && n.id !== other.id));
      let newStatements: any = [];
      if (node.position.y < other.position.y) {
        const otherGivens = other.data.statements.filter((s: any) => s.isGiven);
        const otherProofSteps = other.data.statements.filter((s: any) => !s.isGiven);
        newStatements = [...node.data.statements, ...otherGivens.map((s: any) => {return {value: s.value, isGiven: false}}), ...otherProofSteps]
      } else {
        const nodeGivens = node.data.statements.filter((s: any) => s.isGiven);
        const nodeProofSteps = node.data.statements.filter((s: any) => !s.isGiven);
        newStatements = [...other.data.statements, ...nodeGivens.map((s: any) => {return {value: s.value, isGiven: false}}), ...nodeProofSteps]
      }
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          delete: deleteNodeById,
          id: count,
          type: 'statement',
          statements: newStatements,
          updateStatements: updateStatements,
          addProofStep: addProofStep,
          addGiven: addGiven,
        },
        position: { x: other.position.x, y: other.position.y },
        type: 'textUpdater',
      }]);
      setCount(count + 1);
    }
  }, [nodes]);

  const rfStyle = {
    backgroundColor: '#D0C0F7',
  };

  const background = <Background />;
  const addNode = (nodeType: string) => {
    setNodes([...nodes, {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        delete: deleteNodeById,
        id: count,
        type: nodeType,
        statements: [{ value: '', isGiven: false }],
        updateStatements: updateStatements,
        addProofStep: addProofStep,
        addGiven: addGiven,
      },
      position: { x: 300, y: 0 },
      type: 'textUpdater',
    }]);
    setCount(count + 1);
  };

  return (
    <div>
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('statement')}>Add Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('given')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goal')}>Add Goal</Button>
        </Stack>
      </div>
      <div style={{ height: '85vh', width: '100%' }}>
        <ReactFlow
          nodes={nodes}
          nodeTypes={nodeTypes}
          onNodesChange={onNodesChange}
          edges={edges}
          onEdgesChange={onEdgesChange}
          onConnect={onConnect}
          onNodeDragStop={onNodeDragStop}
          style={rfStyle}
        >
          {background}
          <Controls />
        </ReactFlow>
      </div>
    </div>
  );
}

export default Flow;
