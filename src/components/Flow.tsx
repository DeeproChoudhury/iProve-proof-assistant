import { CloseIcon } from '@chakra-ui/icons';
import { Alert, AlertDescription, AlertIcon, AlertTitle, Button, Grid, GridItem, IconButton, Modal, ModalBody, ModalCloseButton, ModalContent, ModalHeader, ModalOverlay, Spacer, Stack } from '@chakra-ui/react';
import { useCallback, useMemo, useRef, useState } from 'react';
import ReactFlow, {
  Background, Controls, Edge, Node
} from 'reactflow';
import 'reactflow/dist/style.css';
import { makeDeclarationCallbacks } from '../callbacks/declarationsCallbacks';
import { makeFlowCallbacks } from '../callbacks/flowCallbacks';
import { makeInductionNodeCallbacks } from '../callbacks/inductionNodeCallbacks';
import { makeNodeCallbacks } from '../callbacks/nodeCallbacks';
import Z3Solver from '../logic/Solver';
import { IProveError } from '../types/ErrorLocation';
import { AnyNodeType, NodeKind } from '../types/Node';
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
  PopoverBody,
  PopoverArrow,
  PopoverCloseButton,
} from '@chakra-ui/react'
import {
  Table,
  Thead,
  Tbody,
  Tr,
  Th,
  Td,
  TableContainer,
} from '@chakra-ui/react'
import { renderError } from '../util/errors';
import { allParsed, edgesStatus, internalsStatus } from '../util/nodes';
import { SymbolButton } from './SymbolButton';
import { LIQ } from '../logic/LogicInterfaceQueue';

const nodeTypes = {
  proofNode: ProofNode,
  givenNode: GivenNode,
  goalNode: GoalNode,
  inductionNode: InductionNode
};
const edgeTypes = { implication: ImplicationEdge, checked: CheckedEdge, invalid: InvalidEdge };

function Flow() {
  const [proofValid, setProofValid] = useState(true);

  const [nodes, setNodes] = useState<AnyNodeType[]>([]);


  const [edges, setEdges] = useState<Edge[]>([]);
  const [count, setCount] = useState(0);
  const [error, setError] = useState<IProveError | undefined>(undefined);
  const [stopGlobalCheck, setStopGlobalCheck] = useState<boolean | undefined>(undefined);
  const [declarations, setDeclarations] = useState<StatementType[]>([]);
  const [declarationSidebarVisible, setDeclarationSidebarVisible] = useState(true);

  const [typeDeclarations, setTypeDeclarations] = useState<StatementType[]>([]);
  const localZ3Solver = useMemo(() => new Z3Solver.Z3Prover(""), []);

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
  const typeDeclarationsRef = useRef(typeDeclarations);
  typeDeclarationsRef.current = typeDeclarations;

  const nextId = useCallback(() => {
    setCount(count + 1);
    return count;
  }, [count]);

  const checkProofValid = (ns: Node[], es: Edge[]): boolean => {
    const givens = ns.filter(node => node.type === "givenNode");
    const goals = ns.filter(node => node.type === "goalNode");
    const valid = checkValid(ns, goals, givens, es, []);
    return valid;
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

  /* Table used to display 'help' information to user */
  const operatorsToSymbols = [{ value: 'and', symbol: '&' },
  { value: 'or', symbol: '||' },
  { value: 'iff', symbol: '<->' },
  { value: 'implies', symbol: '->' },
  { value: 'for all x', symbol: 'FA x.' },
  { value: 'exists x', symbol: 'EX x.' },
  { value: 'negation', symbol: '~'} ]

  const makeThisNode = useMemo(() => makeNodeCallbacks(nodesRef, edgesRef, setNodes, setEdges, setError, setStopGlobalCheck, localZ3Solver), [localZ3Solver]);
  const makeThisInductionNode = useMemo(() => makeInductionNodeCallbacks(nodesRef, edgesRef, setNodes, setEdges, setError, localZ3Solver), [localZ3Solver]);

  const declarationsCallbacks = useMemo(() => makeDeclarationCallbacks("declarations", setDeclarations, setError), []);
  const typeDeclarationsCallbacks = useMemo(() => makeDeclarationCallbacks("typeDeclarations", setTypeDeclarations, setError), []);

  const flowCallbacks = useMemo(() => makeFlowCallbacks(nodes, setNodes, setEdges, nextId, makeThisNode), [nodes, nextId, makeThisNode]);

  const addNode = useCallback((nodeType: NodeKind) => {
    const count = nextId();
    console.log(nodes);

    if (nodeType === "inductionNode") {
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          internalsStatus: "unchecked",
          edgesStatus: "unchecked",
          types: [{ value: '', wrappers: [] }],
          identifier: [{ value: '', wrappers: [] }],
          inductiveCases: [],
          baseCases: [],
          motive: [{ value: '', wrappers: [] }],
          typeDeclarationsRef,
          thisNode: makeThisInductionNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: 'inductionNode',
      }]);
    }
    else {
      const blankStatement = { value: '', wrappers: [] };
      setNodes(nds => [...nds, {
        id: `${count}`,
        data: {
          label: `Node ${count}`,
          edgesStatus: "unchecked",
          givens: [],
          proofSteps: [],
          goals: nodeType !== 'goalNode' ? [blankStatement] : [],
          thisNode: makeThisNode(`${count}`)
        },
        position: { x: 300, y: 0 },
        type: nodeType,
      }]);
    }

  }, [nextId, makeThisNode, makeThisInductionNode]);


  /**
   * Import Proof given json data. Input list of node data.
   * 
   * @remarks does not need callback?
   */
  const addImportedProof = useCallback((json: any) => {
    // Create Given, Proof, Goal Nodes from input data
    const nodeData = json.nodes.map((node: any) => {
      const id = node.id;
      setCount(Math.max(count, id) + 1);

      if (node.type === "inductionNode") {
        return {
          id: `${id}`,
          data: {
            label: node.data.label,
            allParsed: false,
            internalsValid: false,
            edgesValid: true,
            internalsStatus: "unchecked",
            edgesStatus: "unchecked",
            // inductiveHypotheses: node.data.inductiveHypotheses,
            types: node.data.types,
            thisNode: makeThisInductionNode(`${id}`),

            inductiveCases: node.data.inductiveCases,
            baseCases: node.data.baseCases,
            motive: node.data.motive,

          },
          position: node.position,
          type: node.type,
        }
      } else {
        const n = node;
        n.data.edgesStatus = "unchecked";
        n.data.thisNode = makeThisNode(`${id}`);
        return n;
      }
    });
    
    const edges = json.edges.map((edge: any) => {
      const e = edge;
      e.type = "implication";
      return e;
    })

    setDeclarations(json.declarations);
    setTypeDeclarations(json.types);
    setNodes(nodeData);
    setEdges(edges);

  }, [makeThisNode]);

  const verifyProofGlobal = () => {

    for (const node of nodes) {
      node.data.thisNode.parseAll()
      node.data.thisNode.checkInternal();
      node.data.thisNode.checkEdges();
    }
    LIQ.queue(() => {
      setNodes(nodes => {
        const internalsValid = nodes.every(node => allParsed(node) && internalsStatus(node) === "valid");
        const edgesValid = nodes.every(node => allParsed(node) && edgesStatus(node) === "valid");
        // if problem is with edges don't show anything as there are other errors being displayed
        if (edgesValid && internalsValid) {
          setStopGlobalCheck(false);
        }
        if (edgesValid && !internalsValid) {
          setStopGlobalCheck(true);
        }
        return nodes;
      });
    });
  }

  return (
    <div style={{ position: 'relative' }}>

      {/* START : Modals */}
      {/* START : Import Modal */}
      <Modal isOpen={importModalShow}
        onClose={() => { setImportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalOverlay />
        <ModalContent className="iProveModal">
          <ModalHeader>Import Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalImport addImportedProof={addImportedProof} />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Import Modal */}

      {/* START : Export Modal */}
      <Modal isOpen={exportModalShow}
        onClose={() => { setExportModalShow(false) }}        // onAfterOpen={() => {}}
      >
        <ModalOverlay />
        <ModalContent className="iProveModal">
          <ModalHeader>Export Proof</ModalHeader>
          <ModalCloseButton />
          <ModalBody>
            <ModalExport data={
              JSON.stringify({
                nodes: nodes,
                declarations: declarations,
                types: typeDeclarations,
                edges: edges,
              })
            } />
          </ModalBody>
        </ModalContent>
      </Modal>
      {/* END : Export Modal */}

      

      {/* START : Header*/}
      <div className='header'>
        
      <span className="emBox">
            <span className='highlight'>i</span>Prove
          </span>

        <Stack spacing={4} direction='row' align='center'>
          
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => addNode('givenNode')}>Add Given</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => addNode('goalNode')}>Add Goal</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => addNode('proofNode')}>Add Proof Node</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => addNode('inductionNode')}>Add Induction Node</Button>
          <Button className="headButton" variant="outline" colorScheme='purple' size='md' onClick={() => { setImportModalShow(true) }}>Import Proofs</Button>
          <Button className="headButton" variant="outline" onClick={() => { checkProofValid(nodes, edges); setExportModalShow(true) }}>
            Export proof
          </Button>
          <Button className="headButton" variant="outline" onClick={() => { verifyProofGlobal() }}>
            Verify Entire Proof
          </Button>
          <Button className="headButton" variant="outline" onClick={() => { setDeclarationSidebarVisible(!declarationSidebarVisible) }}>
            {declarationSidebarVisible ? "Hide Sidebar" : "Show Sidebar"}
          </Button>


          {/* START: display table mapping symbol to iprove syntax */}
          <Popover>
            <PopoverTrigger>
              <Button className="headButton" variant="outline" >Symbols</Button>
            </PopoverTrigger>
            <PopoverContent style={{ width: "400px" }}>
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
                      {operatorsToSymbols.map((p, index) =>
                        {
                          return <Tr key={index}>
                            <Td>{p.value}</Td>
                            <Td>
                              <SymbolButton symbol={p.symbol} />
                            </Td>
                          </Tr>;
                        }
                      )}
                    </Tbody>
                  </Table>
                </TableContainer>
              </PopoverBody>
            </PopoverContent>
          </Popover>
          {/* END: display table mapping symbol to iProve syntax */}

          
        </Stack>
      </div>
      {/* END : Header Buttons */}

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
            onClick={() => { setExportModalShow(false) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Export alert */}


      {/* START : Proof valid alert */} 
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
            onClick={() => { setStopGlobalCheck(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Proof valid alert */} 

      {/* START : Proof invalid alert */} 
      <div className="alert-container">
        {stopGlobalCheck === true && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>Error!</AlertTitle>
          <AlertDescription>
            Proof is invalid.
          </AlertDescription>
          <IconButton
            variant='outline'
            aria-label='Add given'
            size='xs'
            onClick={() => { setStopGlobalCheck(undefined) }}
            icon={<CloseIcon />}
          />
        </Alert>}
      </div>
      {/* END : Proof invalid alert */} 

      {/* START : Error alert */} 
      <div className="alert-container">
        {error && <Alert status='error' className="alert">
          <AlertIcon />
          <AlertTitle>{error.kind ?? ""} Error!</AlertTitle>
          <AlertDescription>
            { renderError(error) }
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
      {/* END : Error alert */}

      {/* START : Flow Graph */}
      <div className="flowContainer">
        
        {/* START : Declarations SideBar */}

        <Grid 
          gap={3}
          style={{ marginTop: "20vh", marginLeft: "4vw", zIndex: 20 /* zIndex to move column to front*/ }}             
          visibility={declarationSidebarVisible ? "visible" : "hidden"}
        >

          {/* START : General Declarations */}
          <GridItem >
            <Declarations
              statements={declarations}
              {...declarationsCallbacks}
              />
          </GridItem>
          {/* END : General Declarations */}

          {/* START : Type Declarations */}
          <GridItem>
            <TypeDeclarations
              statements={typeDeclarations}
              {...typeDeclarationsCallbacks}
              />
          </GridItem>
          {/* END : Type Declarations */}

        </Grid>
            
        {/* END : Declarations SideBar */}



        <div className="flowCanvas">
          <ReactFlow
            nodes={(nodes)}
            nodeTypes={nodeTypes}
            edges={edges}
            edgeTypes={edgeTypes}
            disableKeyboardA11y={true} // disable keyboard movemement
            {...flowCallbacks}
          >
            <Background />
            <Controls position='bottom-right' />
          </ReactFlow>
        </div>
      </div>

    </div>
  );
}

export default Flow;
