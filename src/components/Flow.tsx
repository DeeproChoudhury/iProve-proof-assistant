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
import ModalExport from './ModalExport';
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

  /**
   * Modals
   */
  const [importModalShow, setImportModalShow] = useState(false); // show modal for importing proof (see ModalImport.tsx)
  const [exportModalShow, setExportModalShow] = useState(false); // show modal for exporting proof (see ModalExport.tsx)
  
  
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

  
  const addNodeData = useCallback((nodeType: NodeType, givens?: string[], proofs?: string[], goals?: string[]) => {
    const count = nextId();
    setNodes(nds => [...nds, {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        id: count,
        type: nodeType,
        givens: givens === undefined ? [] : givens.map((e) => { return { value: e } }),
        proofSteps: proofs === undefined ? [] : proofs.map((e) => { return { value: e } }),
        goals: goals === undefined ? [] : goals.map((e) => { return { value: e } }),
        declarationsRef,
        thisNode: makeThisNode(`${count}`)
      },
      position: { x: 300, y: 0 },
      type: 'textUpdater',
    }]);
  }, [nextId, makeThisNode]);

  const addNodes = useCallback((jsonNodes: any[]) => {
    const nodeData = jsonNodes.map(node => {
      const newCount = nextId();
      const id = Math.random();
      return {
        id: `${id}`,
        data: {
          label: `Node ${id}`,
          id: id,
          type: node.type,
          givens: node.givens === undefined ? [] : node.givens.map((e: string) => { return { value: e } }),
          proofSteps: node.proofs === undefined ? [] : node.proofs.map((e: string) => { return { value: e } }),
          goals: node.goals === undefined ? [] : node.goals.map((e: string) => { return { value: e } }),
          declarationsRef,
          thisNode: makeThisNode(`${id}`)
        },
        position: { x: 300, y: 0 },
        type: 'textUpdater',
      }
    });
    setNodes(nodeData);
  }, [nextId, makeThisNode]);


  return (
    <div style={{ position: 'relative' }}>

      {/* Declare Modals */}
      {/* Import Modal */}
      <Modal isOpen={importModalShow}        
        onClose={() => {setImportModalShow(false)}}        // onAfterOpen={() => {}}
      >
        <ModalImport/>
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
        <ModalHeader>Import Proof</ModalHeader>
        <ModalCloseButton />
        <ModalBody>
          <ModalImport addNodes={addNodes}/>
        </ModalBody>
        </ModalContent>
      </Modal>

      {/* Export Modal */}
      <Modal isOpen={exportModalShow}        
        onClose={() => {setExportModalShow(false)}}        // onAfterOpen={() => {}}
      >
        <ModalImport/>
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
        <ModalHeader>Export Proof</ModalHeader>
        <ModalCloseButton />
        <ModalBody>
          <ModalExport data={JSON.stringify(nodes.map(n => 
                {return {type: n.data.type, givens: n.data.givens.map(p => p.value), proofs: n.data.proofSteps.map(p => p.value), goals: n.data.goals.map(p => p.value)}}))
          }/>
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
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setError(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>

      <div className="alert-container">
        {error === null && <Alert status='success' className="alert">
          <AlertIcon />
          <AlertTitle>Success!</AlertTitle>
          <AlertDescription>
            Parsing for current node was successful!
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setError(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
    
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('given')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goal')}>Add Goal</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('statement')}>Add Proof Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => {setImportModalShow(true)}}>Import Proofs</Button>
          <Button onClick={() => {setExportModalShow(true)}}>
            Export proof
          </Button>
        </Stack>
      </div>
      <div style={{display: 'flex', flexDirection: 'row'}}>
        <div>
          <Declarations
            statements={declarations} 
            {...declarationsCallbacks}/>
        </div>
        <div style={{ height: '85vh', width: '75%' }}>
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
    </div>
  );
}

export default Flow;
