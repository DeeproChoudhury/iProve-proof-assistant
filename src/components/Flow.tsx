import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, Button, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, Stack } from '@chakra-ui/react';
import { useCallback, useMemo, useRef, useState } from 'react';
import ReactFlow, {
  Background, Controls, Edge, Node
} from 'reactflow';
import 'reactflow/dist/style.css';
import { makeDeclarationCallbacks } from '../callbacks/declarationsCallbacks';
import { makeFlowCallbacks } from '../callbacks/flowCallbacks';
import { makeNodeCallbacks } from '../callbacks/nodeCallbacks';
import Z3Solver from '../solver/Solver';
import { ErrorLocation } from '../types/ErrorLocation';
import { NodeData, NodeType } from '../types/Node';
import { StatementType } from '../types/Statement';
import Declarations from './Declarations';
import CheckedEdge from './edges/CheckedEdge';
import ImplicationEdge from './edges/ImplicationEdge';
import InvalidEdge from './edges/InvalidEdge';
import './Flow.css';
import ModalImport from './ModalImport';
import TextUpdaterNode from './TextUpdaterNode';
import './TextUpdaterNode.css';

const nodeTypes = { textUpdater: TextUpdaterNode };
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge};

function Flow() {
  const [nodes, setNodes] = useState<Node<NodeData>[]>([]);
  const [edges, setEdges] = useState<Edge[]>([]);
  const [count, setCount] = useState(0);
  const [error, setError] = useState<ErrorLocation | undefined>(undefined);
  const [declarations, setDeclarations] = useState<StatementType[]>([]);
  const localZ3Solver = new Z3Solver.Z3Prover("");
  const [importModalShow, setImportModalShow] = useState(false);
  // update refs everytime this hook runs
  const nodesRef = useRef(nodes);
  nodesRef.current = nodes;
  const edgesRef = useRef(edges);
  edgesRef.current = edges;
  const declarationsRef = useRef(declarations);  
  declarationsRef.current = declarations;

  const resetError = () => setError(undefined);

  const nextId = useCallback(() => {
    setCount(count + 1);
    return count;
  }, [count]);

  const makeThisNode = useMemo(() => makeNodeCallbacks(nodesRef, edgesRef, declarationsRef, setNodes, setEdges, setError, localZ3Solver), []);

  const declarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setDeclarations, setError), []);

  const flowCallbacks = useMemo(() => makeFlowCallbacks(nodes, setNodes, setEdges, declarationsRef, nextId, makeThisNode), [nodes, nextId, makeThisNode]);

  const addNode = useCallback((nodeType: NodeType) => {
    const count = nextId();
    setNodes(nds => [...nds, {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        id: count,
        type: nodeType,
        givens: nodeType === 'statement' ? [] : [{ value: '' }],
        proofSteps: [],
        goals: nodeType === 'statement' ? [{ value: '' }] : [], 
        declarationsRef,
        thisNode: makeThisNode(`${count}`)
      },
      position: { x: 300, y: 0 },
      type: 'textUpdater',
    }]);
  }, [nextId, makeThisNode]);

  return (
    
    <div style={{ position: 'relative' }}>
      <Modal isOpen={importModalShow}        
        onClose={() => {setImportModalShow(false)}}        // onAfterOpen={() => {}}
      >
        <ModalImport/>
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
        <ModalHeader>Import Proof</ModalHeader>
        <ModalCloseButton />
        <ModalBody>
          <ModalImport/>
        </ModalBody>
        </ModalContent>
      </Modal>
      
      <div className="alert-container">
        {error && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            {error.column ?
              `Parsing for the last node failed. Error begins at column ${error.column}, from "${error.statement.value}"` : 
              "Parsing for the last node failed. Check your syntax!"
            }
          </AlertDescription>
         
        </Alert>}
      </div>
    
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('given')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goal')}>Add Goal</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('statement')}>Add Proof Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => {setImportModalShow(true)}}>Import Proofs</Button>
        </Stack>
      </div>
      <Declarations
        statements={declarations} 
        {...declarationsCallbacks}/>
      <div style={{ height: '85vh', width: '100%' }}>
        <ReactFlow
          nodes={nodes}
          nodeTypes={nodeTypes}
          edges={edges}
          edgeTypes={edgeTypes}
          disableKeyboardA11y={true} // disable keyboard movemement
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
