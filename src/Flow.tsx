import { useState, useCallback } from 'react';
import { Alert, Button, Stack, AlertIcon, AlertTitle, AlertDescription, IconButton, GlobalStyle } from '@chakra-ui/react'
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
import TextUpdaterNode, { StatementKind, NodeData, NodeType, StatementType, listField } from './TextUpdaterNode';

import './TextUpdaterNode.css';
import './Flow.css';
import { CloseIcon } from '@chakra-ui/icons';
import { evaluate } from './fol-parser';

import ImplicationEdge from './ImplicationEdge';
import CheckedEdge from './CheckedEdge';
import InvalidEdge from './InvalidEdge';
import { Line } from './AST';

type ErrorPosition = {
    columnBegin: number;
    statement: StatementType
}

const initialNodes: Node<NodeData>[] = [];

const initialEdges: Edge[] = [];
const nodeTypes = { textUpdater: TextUpdaterNode };
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge};

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

  function forNodeWithId(nodeId: string, callback: (node: Node<NodeData>) => Node<NodeData>) {
    setNodes(nds => nds.map((nd) => nd.id === nodeId ? callback(nd) : nd));
  }

  function modifyStatementsForNode(nodeId: string, k: StatementKind, callback: (statements: StatementType[]) => StatementType[]) {
    forNodeWithId(nodeId, node => {
      const fieldName = listField(k);
      return {
        ...node,
        data: {
          ...node.data,
          [fieldName]: callback(node.data[fieldName])
        }
      }
    });
  }

  const nodeCallbacks = {
    updateStatement: (nodeId: string, k: StatementKind, statementIndex: number, statement: string) => {
      modifyStatementsForNode(nodeId, k, statements => {
        statements[statementIndex].value = statement;
        statements[statementIndex].parsed = undefined;
        return statements;
      });
    },
    addReasonsToStatement: (nodeId: string, k: StatementKind, statementIndex: number, reasons?: number[]) => {
      modifyStatementsForNode(nodeId, k, statements => {
        statements[statementIndex].reasons = reasons;
        return statements;
      });
    },
    addStatement: (nodeId: string, k: StatementKind) => {
      modifyStatementsForNode(nodeId, k, statements => [...statements, {value: ""}]);
    },
    addStatementAtIndex: (nodeId: string, k: StatementKind, index: number) => {
      modifyStatementsForNode(nodeId, k, statements => {
        statements.splice(index, 0, { value: '' });
        return statements;
      });
    },
    deleteStatementAtIndex: (nodeId: string, k: StatementKind, index: number) => {
      modifyStatementsForNode(nodeId, k, statements => {
        statements.splice(index, 1);
        return statements;
      });
    },
    checkSyntax: (nodeId: string) => {
      setNodes(nds => nds.map((node) => {
        let errorDetected = false;
        if (node.id === nodeId && node?.data !== undefined) {

          const updateWithParsed = (statement: StatementType, index: number) => {
            const parsedOrError = evaluate(statement.value);
            if(parsedOrError.kind === "Error") {
              statement.syntaxCorrect = false;
              errorDetected = true;
              setErrorPosition(parsedOrError.pos ? { columnBegin: parsedOrError.pos.columnBegin, statement: statement } : undefined);
              setSyntaxError(true);
              setParseSuccessful(false);
            } else {
              console.log(parsedOrError);
              statement.parsed = parsedOrError as Line; // TODO: avoid cast here?
              statement.syntaxCorrect = true;
            }
            return statement;
          };

          const newGivens: StatementType[] = node.data.givens.map(updateWithParsed);
          const newGoals: StatementType[] = node.data.goals.map(updateWithParsed);
          const newProofSteps: StatementType[] = node.data.proofSteps.map(updateWithParsed);
          node.data = {
            ...node.data,
            givens: newGivens,
            proofSteps: newProofSteps,
            goals: newGoals
          }

          if (!errorDetected) {
            setSyntaxError(false);
            setParseSuccessful(true);
          }
        }
        return node;
      }));
    },
    checkEdges: (nodeId: string) => {
      // here we should get all incoming edges & nodes to nodeID
      // use the proofSteps (maybe goals?) of the incoming nodes and the givens of nodeId
      // to deduce whether the implication holds (using z3)
      // if yes, set correctImplication = true and mark all edges + nodeId as true
      let correctImplication = false;
      setEdges(eds => {
        setNodes(nds => { 

          const incomingEdges = eds.filter((e) => e.target === nodeId);
          // get all nodes that have incoming edge to nodeId
          // should probably use getIncomers from reactflow
          const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
          const incomingNodes = nds.filter(node => incomingNodesIds.has(node.id))
          const givens = incomingNodes.map(node => getResults(node)).reduce((acc,v) => acc.concat(v), [])
          const exp_implications = nds.filter(node => node.id === nodeId)[0].data.givens
          
          // check that exp_implications follows from givens with z3
          correctImplication = Math.random() > 0.5;

          //set nodes
          return nds.map((node) => {
            if (node.id == nodeId) {
              node.data = {
                ...node.data,
                correctImplication: correctImplication
              }
            }
            return node;
          });
        });

        //set edges
        return eds.map((edge) => {
          if (edge.target === nodeId) {
            edge.type = correctImplication ? "checked" : "invalid";
          }
          return edge;
        });
      });
    }
  }

  const getResults = (node: Node) => {
    if (node.data.type === "statement") {
      return node.data.goals;
    } else if (node.data.type === "given") {
      return node.data.givens;
    } 
  }

  const onConnect = useCallback(
    (params: Connection) => {
      setEdges((eds) => addEdge({...params, 
        type:"implication", 
        id: `${params.source}-${params.target}`,
      }, eds));
    }, []);

  const deleteNodeById = (id: string) => {
    setNodes(nds => nds.filter(node => node.id !== id));
  };

  const collided = (node1: Node, node2: Node): boolean => {
    const a: number = node1.position.x - node2.position.x;
    const b: number = node1.position.y - node2.position.y;
    return Math.sqrt(a * a + b * b) < 100;
  }

  const onNodeDragStop = useCallback((event: React.MouseEvent, node: Node, selectedNodes: Node[]) => {
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
      let goals: StatementType[] = []
      if (node.position.y < other.position.y) {
        givens = node.data.givens;
        proofSteps = [...node.data.proofSteps, ...node.data.goals, ...other.data.givens, ...other.data.proofSteps];
        goals = other.data.goals;
      } else {
        givens = other.data.givens;
        proofSteps = [...other.data.proofSteps, ...other.data.goals, ...node.data.givens, ...node.data.proofSteps];
        goals = node.data.goals;
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
          goals: goals, 
          ...nodeCallbacks
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
      const proofSteps: StatementType[] = [];
      const goals = nodeType === 'statement' ? [{ value: '' }] : [];
      return [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          delete: deleteNodeById,
          id: count,
          type: nodeType,
          givens: givens,
          proofSteps: proofSteps,
          goals: goals, 
          ...nodeCallbacks
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
          edgeTypes={edgeTypes}
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
