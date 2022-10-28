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
import TextUpdaterNode, { NodeData, NodeType, StatementType } from './TextUpdaterNode';

import './TextUpdaterNode.css';
import './Flow.css';
import { CloseIcon } from '@chakra-ui/icons';
import { evaluate } from './fol-parser';

type ErrorPosition = {
    columnBegin: number;
    statement: StatementType
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

  const updateGivens = (nodeId: string, statementIndex: number, statement: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        const newStatements = node.data.givens;
        newStatements[statementIndex].value = statement;
        node.data = {
          ...node.data,
          givens: newStatements,
        };
      }
      return node;
    }));
  };

  const updateProofSteps = (nodeId: string, statementIndex: number, statement: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        const newStatements = node.data.proofSteps;
        newStatements[statementIndex].value = statement;
        node.data = {
          ...node.data,
          proofSteps: newStatements,
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
          givens: [...node.data.givens, { value: '' }],
        };
      }
      return node;
    }));
  }

  const checkSyntax = (nodeId: string) => {
    setNodes(nds => nds.map((node) => {
      let errorDetected = false;
      if (node.id === nodeId && node?.data !== undefined) {
        const newGivens: StatementType[] = node.data.givens.map((statement: StatementType, index: number) => {
          try {
            const parsed = evaluate(statement.value);
            console.log(parsed);
            statement.parsed = parsed;
            statement.syntaxCorrect = true;
          } catch (e: any) {
            statement.syntaxCorrect = false;
            errorDetected = true;
            setErrorPosition(e.pos === undefined ? undefined : { columnBegin: e.pos.columnBegin, statement: statement });
            if (e instanceof Error) {
              setSyntaxError(true);
              setParseSuccessful(false);
            }
          }
          return statement;
        })
        const newProofSteps: StatementType[] = node.data.proofSteps.map((statement: StatementType, index: number) => {
          try {
            const parsed = evaluate(statement.value);
            console.log(parsed);
            statement.parsed = parsed;
            statement.syntaxCorrect = true;
          } catch (e: any) {
            statement.syntaxCorrect = false;
            errorDetected = true;
            setErrorPosition(e.pos === undefined ? undefined : { columnBegin: e.pos.columnBegin, statement: statement });
            if (e instanceof Error) {
              setSyntaxError(true);
              setParseSuccessful(false);
            }
          }
          return statement;
        })
        node.data = {
          ...node.data,
          givens: newGivens,
          proofSteps: newProofSteps,
        }
        
        if (!errorDetected) {
          setSyntaxError(false);
          setParseSuccessful(true);
        }
      }
      return node;
    }));
  }

  const addProofStep = (nodeId: string) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        node.data = {
          ...node.data,
          proofSteps: [...node.data.proofSteps, { value: '' }],
        };
      }
      return node;
    }));
  }

  const addStatementAtIndex = (nodeId: string, index: number, isGiven: boolean) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        const newStatements = isGiven ? node.data.givens : node.data.proofSteps;
        newStatements.splice(index, 0, { value: '' });
        if (isGiven) {
          node.data = {
            ...node.data,
            givens: newStatements,
          };
        } else {
          node.data = {
            ...node.data,
            proofSteps: newStatements,
          };
        }
      }
      return node;
    }));
  }

  const deleteStatementAtIndex = (nodeId: string, index: number, isGiven: boolean) => {
    setNodes(nds => nds.map((node) => {
      if (node.id === nodeId) {
        const newStatements = isGiven ? node.data.givens : node.data.proofSteps;
        newStatements.splice(index, 1);
        if (isGiven) {
          node.data = {
            ...node.data,
            givens: newStatements,
          };
        } else {
          node.data = {
            ...node.data,
            proofSteps: newStatements,
          };
        }
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
      let givens: StatementType[] = [];
      let proofSteps: StatementType[] = [];
      if (node.position.y < other.position.y) {
        givens = node.data.givens;
        proofSteps = [...node.data.proofSteps, ...other.data.givens, ...other.data.proofSteps];
      } else {
        givens = other.data.givens;
        proofSteps = [...other.data.proofSteps, ...node.data.givens, ...node.data.proofSteps];
      }
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          delete: deleteNodeById,
          id: count,
          type: 'statement',
          givens: givens,
          proofSteps: proofSteps,
          updateGivens: updateGivens,
          updateProofSteps: updateProofSteps,
          addProofStep: addProofStep,
          addGiven: addGiven,
          addStatementAtIndex: addStatementAtIndex,
          checkSyntax: checkSyntax,
          deleteStatementAtIndex: deleteStatementAtIndex,
        },
        position: { x: other.position.x, y: other.position.y },
        type: 'textUpdater',
      }]);
      setCount(count + 1);
    }
  }, [nodes, count]);

  const background = <Background />;
  const addNode = (nodeType: NodeType) => {
    setNodes(nds => {
      const givens = nodeType === 'statement' ? [] : [{ value: '' }];
      const proofSteps = nodeType === 'statement' ? [{ value: '' }] : [];
      return [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          delete: deleteNodeById,
          id: count,
          type: nodeType,
          givens: givens,
          proofSteps: proofSteps,
          updateGivens: updateGivens,
          updateProofSteps: updateProofSteps,
          addProofStep: addProofStep,
          addGiven: addGiven,
          addStatementAtIndex: addStatementAtIndex,
          checkSyntax: checkSyntax,
          deleteStatementAtIndex: deleteStatementAtIndex,
        },
        position: { x: 300, y: 0 },
        type: 'textUpdater',
      }]
    });
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
