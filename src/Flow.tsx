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
import Declarations from './Declarations';

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
  const [declarations, setDeclarations] = useState<StatementType[]>([]);

  const forNodeWithId = (nodeId: string, callback: (node: Node<NodeData>, nodes: Node<NodeData>[]) => Node<NodeData>) => {
    setNodes(nds => nds.map((nd) => nd.id === nodeId ? callback(nd, nds) : nd));
  }

  const modifyStatementsForNode = (nodeId: string, k: StatementKind, callback: (statements: StatementType[]) => StatementType[]) => {
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

  const getResults = (node: Node<NodeData>): StatementType[] => {
    switch (node.data.type) {
      case "given": return node.data.givens;
      case "statement": return node.data.goals;
      case "goal": return [];
    }
  }

  const collided = (node1: Node, node2: Node): boolean => {
    const a: number = node1.position.x - node2.position.x;
    const b: number = node1.position.y - node2.position.y;
    return Math.sqrt(a * a + b * b) < 100;
  }

  const nodeCallbacks = {
    deleteNode: (nodeId: string) => {
      setNodes(nds => nds.filter(node => node.id !== nodeId));
    },
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
      forNodeWithId(nodeId, node => {
        if (!node.data) return node;

        let errorDetected = false;
        const updateWithParsed = (statement: StatementType) => {
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

        if (!errorDetected) {
          setSyntaxError(false);
          setParseSuccessful(true);
        }
        return {
          ...node,
          data: {
            ...node.data,
            givens: node.data.givens.map(updateWithParsed),
            proofSteps: node.data.proofSteps.map(updateWithParsed),
            goals: node.data.goals.map(updateWithParsed)
          }
        };
      });
    },
    checkEdges: (nodeId: string) => {
      // here we should get all incoming edges & nodes to nodeID
      // use the proofSteps (maybe goals?) of the incoming nodes and the givens of nodeId
      // to deduce whether the implication holds (using z3)
      // if yes, set correctImplication = true and mark all edges + nodeId as true
      let correctImplication = false;
      setEdges(eds => {
        forNodeWithId(nodeId, (node, nds) => {
          const incomingEdges = eds.filter((e) => e.target === nodeId);
          // get all nodes that have incoming edge to nodeId
          // should probably use getIncomers from reactflow
          const incomingNodesIds = new Set(incomingEdges.map((e) => e.source));
          const incomingNodes = nds.filter(node => incomingNodesIds.has(node.id))
          const givens = incomingNodes.map(node => getResults(node)).flat();
          const exp_implications = node.data.givens;
          
          // check that exp_implications follows from givens with z3
          correctImplication = Math.random() > 0.5;

          //set nodes
          return {
            ...node,
            data: {
              ...node.data,
              correctImplication
            }
          };
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
  };
  
  const flowCallbacks = {
    onNodeDragStop: useCallback((event: React.MouseEvent, node: Node, selectedNodes: Node[]) => {
      if (node.data.type !== 'statement') return;

      const other: Node<NodeData> | undefined = nodes
        .filter((other) => other.data.type === 'statement')
        .find((other) => other.id !== node.id && collided(node, other));

      if (!other) return;

      const [first, second] = node.position.y < other.position.y ? [node, other] : [other, node];
      setNodes(nds => [...nds.filter(n => n.id !== node.id && n.id !== other.id), {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          id: count,
          type: 'statement',
          givens: first.data.givens,
          proofSteps: [
            ...first.data.proofSteps,
            ...first.data.goals,
            ...second.data.givens,
            ...second.data.proofSteps
          ],
          goals: second.data.goals,
          ...nodeCallbacks
        },
        position: { x: other.position.x, y: other.position.y },
        type: 'textUpdater',
      }]);
      setCount(count + 1);
    }, [nodes, count]),
    onNodesChange: useCallback(
      (changes: NodeChange[]) => setNodes((nds) => applyNodeChanges(changes, nds)),
      []
    ),
    onEdgesChange: useCallback(
      (changes: EdgeChange[]) => setEdges((eds) => applyEdgeChanges(changes, eds)),
      []
    ),
    onConnect: useCallback((params: Connection) => {
      setEdges((eds) => addEdge({...params, 
        type:"implication", 
        id: `${params.source}-${params.target}`,
      }, eds));
    }, [])
  };

  const addNode = (nodeType: NodeType) => {
    setNodes(nds => [...nds, {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        id: count,
        type: nodeType,
        givens: nodeType === 'statement' ? [] : [{ value: '' }],
        proofSteps: [],
        goals: nodeType === 'statement' ? [{ value: '' }] : [], 
        ...nodeCallbacks
      },
      position: { x: 300, y: 0 },
      type: 'textUpdater',
    }]);
    setCount(count + 1);
  };

  const addDeclaration = (index: number) => {
    setDeclarations(decl => [...decl.slice(0, index), {value: ''}, ...decl.slice(index)]);
  };

  const deleteDeclaration = (index: number) => {
    setDeclarations(decl => decl.filter((d, i) => i !== index))
  };

  const updateDeclaration = (index: number, declaration: string) => {
    setDeclarations((decls) => decls.map((decl, i) => {
      if (i === index) {
       decl.value = declaration
       decl.parsed = undefined; 
      }
      return decl;
    }));
  };

  const checkDeclarationSyntax = () => {
    setDeclarations(decls => decls.map((declaration, index) => {
      let errorDetected = false;
      const updateWithParsed = (statement: StatementType) => {
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

      if (!errorDetected) {
        setSyntaxError(false);
        setParseSuccessful(true);
      }
      return updateWithParsed(declaration);
    }))
  }

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
          <Button colorScheme='purple' size='md' onClick={() => addNode('given')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goal')}>Add Goal</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('statement')}>Add Proof Node</Button>
        </Stack>
      </div>
      <Declarations 
        statements={declarations} 
        addDeclaration={addDeclaration} 
        deleteDeclaration={deleteDeclaration} 
        updateDeclaration={updateDeclaration}
        checkSyntax={checkDeclarationSyntax}/>
      <div style={{ height: '85vh', width: '100%' }}>
        <ReactFlow
          nodes={nodes}
          nodeTypes={nodeTypes}
          edges={edges}
          edgeTypes={edgeTypes}
          {...flowCallbacks}
        >
          <Background />
          <Controls />
        </ReactFlow>
      </div>
    </div>
  );
}

export default Flow;
