import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, Button, Grid, GridItem, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, Stack } from '@chakra-ui/react';
import { useCallback, useMemo, useRef, useState } from 'react';
import ReactFlow, {
  Background, Controls, Edge, Node
} from 'reactflow';
import 'reactflow/dist/style.css';
import { makeDeclarationCallbacks } from '../callbacks/declarationsCallbacks';
import { makeFlowCallbacks } from '../callbacks/flowCallbacks';
import { makeInductionNodeCallbacks } from '../callbacks/inductionNodeCallbacks';
import { makeNodeCallbacks } from '../callbacks/nodeCallbacks';
import Z3Solver from '../solver/Solver';
import { ErrorLocation } from '../types/ErrorLocation';
import { InductionNodeType, NodeType, StatementNodeType } from '../types/Node';
import { StatementType } from '../types/Statement';
import Declarations from './Declarations';
import CheckedEdge from './edges/CheckedEdge';
import ImplicationEdge from './edges/ImplicationEdge';
import InvalidEdge from './edges/InvalidEdge';
import './Flow.css';
import ModalExport from './ModalExport';
import ModalImport from './ModalImport';
import GivenNode from './nodes/GivenNode';
import GoalNode from './nodes/GoalNode';
import InductionNode from './nodes/InductionNode';
import ProofNode from './nodes/ProofNode';
import './nodes/ProofNode.css';
import TypeDeclarations from './TypeDeclarations';
import {
  Popover,
  PopoverTrigger,
  PopoverContent,
  PopoverHeader,
  PopoverBody,
  PopoverFooter,
  PopoverArrow,
  PopoverCloseButton,
  PopoverAnchor,
} from '@chakra-ui/react'
import {
  Table,
  Thead,
  Tbody,
  Tfoot,
  Tr,
  Th,
  Td,
  TableCaption,
  TableContainer,
} from '@chakra-ui/react'

const nodeTypes = { 
  proofNode: ProofNode,
  givenNode: GivenNode,
  goalNode: GoalNode,
  inductionNode: InductionNode
};
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge};

function Flow() {
  const [proofValid, setProofValid] = useState(false);
  
  const [nodes, setNodes] = useState<StatementNodeType[]>([]);
  const [inductionNodes, setInductionNodes] = useState<InductionNodeType[]>([]);
  

  const [edges, setEdges] = useState<Edge[]>([]);
  const [count, setCount] = useState(0);
  const [error, setError] = useState<ErrorLocation | undefined>(undefined);  
  const [stopGlobalCheck, setStopGlobalCheck] = useState<boolean | undefined>(undefined);
  const [declarations, setDeclarations] = useState<StatementType[]>([]);
  const [declarationSidebarVisible, setDeclarationSidebarVisible] = useState(true);

  const [typeDeclarations, setTypeDeclarations] = useState<StatementType[]>([]);

  const [typeSidebarVisible, setTypeSidebarVisible] = useState(true);
  const localZ3Solver = useMemo(() => new Z3Solver.Z3Prover(""), []);

  /**
   * Modals
   */
  const [importModalShow, setImportModalShow] = useState(false); // show modal for importing proof (see ModalImport.tsx)
  const [exportModalShow, setExportModalShow] = useState(false); // show modal for exporting proof (see ModalExport.tsx)

  // update refs everytime this hook runs
  const nodesRef = useRef(nodes);
  nodesRef.current = nodes;
  const inductionNodesRef = useRef(inductionNodes);
  inductionNodesRef.current = inductionNodes;
  const edgesRef = useRef(edges);
  edgesRef.current = edges;
  const declarationsRef = useRef(declarations);  
  declarationsRef.current = declarations;
  const typeDeclarationsRef = useRef(typeDeclarations);  
  typeDeclarationsRef.current = typeDeclarations;

  const nextId = useCallback(() => {
    setCount(count + 1);
    return count;
  }, [count]);

  const checkProofValid = (ns: Node[], es: Edge[]): void => {
    const givens = ns.filter( node => node.type === "givenNode");
    const goals = ns.filter( node => node.type === "goalNode");
    setProofValid(checkValid(ns, goals, givens, es, []));
  }
  
  const checkValid = (ns: Node[], currs: Node[], givens: Node[], es: Edge[], visited: Node[]): boolean => {
    // check that all paths into goals eventually start at givens and only use valid edges and do not cycle
    const non_given_currs = currs.filter(node => !givens.includes(node));
    const cycle_found = non_given_currs.some(n => visited.includes(n)); //check if any current node has already been found
    if (cycle_found) {
      console.log("here3");
      return false;
    }
    const new_visited = visited.concat(non_given_currs);
    const non_given_currs_ids = non_given_currs.map(node => node.id);
    if (non_given_currs_ids.length === 0) {
      return true
    }
    const valid_edges_to_non_given_currs: Edge[] = es.filter(e => non_given_currs_ids.includes(e.target));
    const prev_ids = valid_edges_to_non_given_currs.map(e => e.source);
    const hit_currs = valid_edges_to_non_given_currs.map(e => e.target);
    const no_incoming_edges_non_givens = non_given_currs_ids.filter(id => !hit_currs.includes(id));
    if (no_incoming_edges_non_givens.length > 0) {
      console.log("here2");
      return false; //path can't end at a non_given node
    }
    const prev_nodes = ns.filter(node => prev_ids.includes(node.id));
    if (prev_nodes.length === 0) {
      console.log("here1");
      return false;
    } else {
      return checkValid(ns, prev_nodes, givens, es, new_visited);
    }
  }

  const makeThisNode = useMemo(() => makeNodeCallbacks(nodesRef, edgesRef, declarationsRef, setNodes, setEdges, setError, setStopGlobalCheck, localZ3Solver), [localZ3Solver]);
  const makeThisInductionNode = useMemo(() => makeInductionNodeCallbacks(inductionNodesRef, edgesRef, declarationsRef, setInductionNodes, setEdges, setError, localZ3Solver), [localZ3Solver]);

  const declarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setDeclarations, setError), []);
  const typeDeclarationsCallbacks = useMemo(() => makeDeclarationCallbacks(setTypeDeclarations, setError), []);

  const flowCallbacks = useMemo(() => makeFlowCallbacks(nodes, inductionNodes, setNodes, setInductionNodes, setEdges, declarationsRef, nextId, makeThisNode), [nodes, inductionNodes, nextId, makeThisNode]);

  const addSymbol = (symbol: String): void => {
    console.log(symbol);
  };

  const addNode = useCallback((nodeType: NodeType) => {
    const count = nextId();
    
    if (nodeType === "inductionNode") {
      setInductionNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          types: [{value: '', wrappers: []}],
          predicate: [{value: '', wrappers: []}],
          inductiveCases: [],
          baseCases: [],
          inductiveHypotheses: [{value: '', wrappers: []}],
          declarationsRef,
          typeDeclarationsRef,
          thisNode: makeThisInductionNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: 'inductionNode',
      }]);
    }
    else {
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          givens: nodeType === 'proofNode' ? [] : [{ value: '', wrappers: []}],
          proofSteps: [],
          goals: nodeType === 'proofNode' ? [{ value: '', wrappers: []}, ] : [], 
          declarationsRef,
          thisNode: makeThisNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: nodeType,
      }]);
    }
    
  }, [nextId, makeThisNode, makeThisInductionNode]);

  
  const addNodeData = useCallback((nodeType: Exclude<NodeType, "inductionNode">, givens?: string[], proofs?: string[], goals?: string[]) => {
    const count = nextId();
    setNodes(nds => [...nds, {
      id: `${count}`,
      data: {
        label: `Node ${count}`,
        givens: givens === undefined ? [] : givens.map((e) => { return { value: e, wrappers: []} }),
        proofSteps: proofs === undefined ? [] : proofs.map((e) => { return { value: e, wrappers: [] } }),
        goals: goals === undefined ? [] : goals.map((e) => { return { value: e, wrappers: [] } }),
        declarationsRef,
        thisNode: makeThisNode(`${count}`)
      },
      position: { x: 300, y: 0 },
      type: nodeType,
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
          givens: node.givens === undefined ? [] : node.givens.map((e: string) => { return { value: e, wrappers: [] } }),
          proofSteps: node.proofs === undefined ? [] : node.proofs.map((e: string) => { return { value: e, wrappers: [] } }),
          goals: node.goals === undefined ? [] : node.goals.map((e: string) => { return { value: e, wrappers: [] } }),
          declarationsRef,
          thisNode: makeThisNode(`${id}`)
        },
        position: { x: 300, y: 0 },
        type: node.type,
      }
    });
    if (jsonNodes.length > 0) {
      const declarationsData = [jsonNodes[0].dec].map(d => {
        return {
          value : d,
          wrappers: []
        }
      });
      const typeDeclarations = [jsonNodes[0]].map(node => {
        return {
          value : node.types,
          wrappers: []
        }
      });;
      setDeclarations(declarationsData);
      setTypeDeclarations(typeDeclarations);
    }
    
    setNodes(nodeData);
  }, [nextId, makeThisNode]);

  const verifyProofGlobal = async () => {
    /* check all nodes have correct syntax */ 
    setStopGlobalCheck(undefined);
    for await (const node of nodes) {
      // check might not be necessary with the onBlur, but better make sure
      await node.data.thisNode.checkSyntax();
    }
    let correctEdges = true;
    for await (const node of nodes) {
      if (node.type !== "givenNode") {
        const output = await node.data.thisNode.checkEdges();
        correctEdges = correctEdges && output;
      }
    }
    for await (const node of nodes) {
      await node.data.thisNode.checkInternalAssertions();
    }
    setStopGlobalCheck(stop => {
      return !(stop === undefined && correctEdges);
    })
  }

  return (
    <div style={{ position: 'relative' }}>

      {/* START : Modals */}
      {/* START : Import Modal */}
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
      {/* END : Import Modal */}

      {/* START : Export Modal */}
      <Modal isOpen={exportModalShow && proofValid}        
        onClose={() => {setExportModalShow(false)}}        // onAfterOpen={() => {}}
      >
        <ModalImport/>
        <ModalContent style={{ backgroundColor: "rgb(56, 119, 156)", color: 'white' }}>
        <ModalHeader>Export Proof</ModalHeader>
        <ModalCloseButton />
        <ModalBody>
          <ModalExport data={JSON.stringify(nodes.map(n => 
                {return {type: n.type, givens: n.data.givens.map(p => p.value), proofs: n.data.proofSteps.map(p => p.value), goals: n.data.goals.map(p => p.value)}}))
          }/>
        </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Export Modal */}

      {/* START : Export alert */}
      <div className="alert-container">
        {exportModalShow && !proofValid && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof can not be printed as proof is not valid. 
            For a proof graph to be valid, all paths into goal nodes must start at a given node, 
            only use valid edges and be acyclical.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => {setExportModalShow(false)}}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>


      {/* START : Incorrect proof alert */}
      <div className="alert-container">
        {stopGlobalCheck === true && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof is not valid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => {setStopGlobalCheck(undefined)}}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      <div className="alert-container">
        {stopGlobalCheck === false && <Alert status='success' className="alert">
          <AlertIcon />
          <AlertTitle>Success!</AlertTitle>
          <AlertDescription>
            Proof is valid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => {setStopGlobalCheck(undefined)}}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Incorrect Proof */}
      
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
        {error === null && 
        <Alert status='success' className="alert">
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
      {/* END : Export alert */}
    
      {/* START : Header Buttons */}
      <div>
        <Stack style={{ marginLeft: '1em', marginBottom: '1em' }} spacing={4} direction='row' align='center'>
          <Button colorScheme='purple' size='md' onClick={() => addNode('givenNode')}>Add Given</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('goalNode')}>Add Goal</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('proofNode')}>Add Proof Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => addNode('inductionNode')}>Add Induction Node</Button>
          <Button colorScheme='purple' size='md' onClick={() => {setImportModalShow(true)}}>Import Proofs</Button>
          <Button onClick={() => {checkProofValid(nodes, edges); setExportModalShow(true)}}>
            Export proof
          </Button>
          <Button onClick={() => {verifyProofGlobal()}}>
            Verify Entire Proof
          </Button>
          <Button onClick={() => {setDeclarationSidebarVisible(!declarationSidebarVisible)}}>
            Settings
          </Button>
          <Popover>
            <PopoverTrigger>
              <Button>Symbols</Button>
            </PopoverTrigger>
            <PopoverContent style = {{width:"400px"}}>
              <PopoverArrow />
              <PopoverCloseButton />
              <PopoverBody>
              <TableContainer>
                <Table variant='simple'>
                  <Thead>
                    <Tr>
                      <Th>Logical Operator</Th>
                      <Th>iProve Symbol</Th>
                    </Tr>
                  </Thead>
                  <Tbody>
                    <Tr>
                      <Td>and</Td>
                      <Td>&</Td>
                    </Tr>
                    <Tr>
                      <Td>or</Td>
                      <Td></Td>
                    </Tr>
                    <Tr>
                      <Td>iff</Td>
                      <Td>{"<->"}</Td>
                    </Tr>
                    <Tr>
                      <Td>implies</Td>
                      <Td>{"->"}</Td>
                    </Tr>
                    <Tr>
                      <Td>for all x</Td>
                      <Td>FA x.</Td>
                    </Tr>
                    <Tr>
                      <Td>exists x</Td>
                      <Td>E x.</Td>
                    </Tr>
                  </Tbody>
                </Table>
              </TableContainer>
              </PopoverBody>
            </PopoverContent>
          </Popover>
        </Stack>
      </div>
      {/* END : Header Buttons */}


      {/* START : Flow Graph */}
      <div style={{display: 'flex', flexDirection: 'row', height:"100vh" }}>
        {/* START : Column for declarations */}
        <Grid style={{zIndex: 20 /* zIndex to move column to front*/}} 
          // templateRows='repeat(3, 1fr)'
          gap={3}
          visibility={declarationSidebarVisible ? "visible" : "hidden"}
        >
          
          {/* START : General Declarations */}
          <GridItem >
              <Declarations
                statements={declarations} 
                {...declarationsCallbacks}
                visible={true}/>
          </GridItem>
          {/* END : General Declarations */}
          
          {/* START : Type Declarations */}
          <GridItem>
            <TypeDeclarations
              statements={typeDeclarations} 
              {...typeDeclarationsCallbacks}
              visible={true}/>
          </GridItem>
          {/* END : Type Declarations */}

        </Grid>
        {/* END : Column for declarations */}


        <div style={{ height: '85vh', width: '100%' }}>
          <ReactFlow
            nodes={(nodes as Node[]).concat(inductionNodes as Node[])}
            nodeTypes={nodeTypes}
            edges={edges}
            edgeTypes={edgeTypes}
            disableKeyboardA11y={true} // disable keyboard movemement
            {...flowCallbacks}
          >
            <Background />
            <Controls position='bottom-right'/>
          </ReactFlow>
        </div>
      </div>

    </div>
  );
}

export default Flow;
