import { useState, useCallback } from 'react';
import { Alert, Button, Stack, AlertIcon, AlertTitle, AlertDescription, IconButton } from '@chakra-ui/react'
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
import TextUpdaterNode, { NodeData, NodeType, Statement } from './TextUpdaterNode';

import './TextUpdaterNode.css';
import './Flow.css';
import { CloseIcon } from '@chakra-ui/icons';
import { evaluate } from './fol-parser';

type ErrorPosition = {
    columnBegin: number;
    statement: Statement
}

const initialNodes: Node<NodeData>[] = [];

const initialEdges: Edge[] = [];
const nodeTypes = { textUpdater: TextUpdaterNode };

function Flow() {
  const [nodes, setNodes] = useState(initialNodes);
  const [edges, setEdges] = useState(initialEdges);
  const [count, setCount] = useState(0);
  const [syntaxError, setSyntaxError] = useState(false);
  const [parseSuccessful, setParseSuccessful] = useState(false);
  const [errorPosition, setErrorPosition] = useState<ErrorPosition | undefined>(undefined);

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

  const checkSyntax = (nodeId: string) => {
    setNodes(nds => {
      const node = nds.find((n) => n.id === nodeId);
      let errorDetected = false;
      if (node?.data !== undefined) {
        for (var statement of node.data.statements) {
          try {
            const parsed = evaluate(statement.value);
            console.log(parsed);
            statement.parsed = parsed;
          } catch (e: any) {
            errorDetected = true;
            setErrorPosition(e.pos === undefined ? undefined : {columnBegin: e.pos.columnBegin, statement});
            if (e instanceof Error) {
              setSyntaxError(true);
              setParseSuccessful(false);
            }
          }
        }
        if (!errorDetected) {
          setSyntaxError(false);
          setParseSuccessful(true);
        }
      }
      return nds;
    })
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
    const other: Node<NodeData> | undefined =
      nodes.filter((other) => other.data.type === 'statement')
        .find((other) => other.id !== node.id && collided(node, other));
    if (other !== undefined) {
      setNodes(nds => nds.filter(n => n.id !== node.id && n.id !== other.id));
      let newStatements: Statement[] = [];
      if (node.position.y < other.position.y) {
        const otherGivens = other.data.statements.filter((s: Statement) => s.isGiven);
        const otherProofSteps = other.data.statements.filter((s: Statement) => !s.isGiven);
        newStatements = [...node.data.statements, ...otherGivens.map((s: Statement) => { return { value: s.value, isGiven: false } }), ...otherProofSteps]
      } else {
        const nodeGivens = node.data.statements.filter((s: Statement) => s.isGiven);
        const nodeProofSteps = node.data.statements.filter((s: Statement) => !s.isGiven);
        newStatements = [...other.data.statements, ...nodeGivens.map((s: Statement) => { return { value: s.value, isGiven: false } }), ...nodeProofSteps]
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
          checkSyntax: checkSyntax,
        },
        position: { x: other.position.x, y: other.position.y },
        type: 'textUpdater',
      }]);
      setCount(count + 1);
    }
  }, [nodes, count]);

  const background = <Background />;
  const addNode = (nodeType: NodeType) => {
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
        checkSyntax: checkSyntax,
      },
      position: { x: 300, y: 0 },
      type: 'textUpdater',
    }]);
    setCount(count + 1);
  };

  return (
    <div style={{ position: 'relative' }}>
      <div className="alert-container">
        {syntaxError && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            {errorPosition === undefined ?
              "Parsing for the last node failed. Check your syntax!" :
              `Parsing for the last node failed. Error begins at column ${errorPosition.columnBegin}, from "${errorPosition.statement.value}"`}
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setSyntaxError(false) }}
            icon={<CloseIcon />}
          />
        </Alert>}
        {!syntaxError && parseSuccessful && <Alert status='success' className="alert">
          <AlertIcon />
          <AlertTitle>Success!</AlertTitle>
          <AlertDescription>
            Parsing for current node was successful!
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setParseSuccessful(false) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('statement')}>Add Proof Node</Button>
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
        >
          {background}
          <Controls />
        </ReactFlow>
      </div>
    </div>
  );
}

export default Flow;
